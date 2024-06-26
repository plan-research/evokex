/*
 * Copyright (C) 2010-2018 Gordon Fraser, Andrea Arcuri and EvoSuite
 * contributors
 *
 * This file is part of EvoSuite.
 *
 * EvoSuite is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3.0 of the License, or
 * (at your option) any later version.
 *
 * EvoSuite is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with EvoSuite. If not, see <http://www.gnu.org/licenses/>.
 */
package org.evosuite.ga.metaheuristics.mosa;

import kotlin.jvm.functions.Function0;
import org.evosuite.Properties;
import org.evosuite.coverage.line.LineCoverageTestFitness;
import org.evosuite.ga.ChromosomeFactory;
import org.evosuite.ga.comparators.OnlyCrowdingComparator;
import org.evosuite.ga.metaheuristics.mosa.structural.MultiCriteriaManager;
import org.evosuite.ga.operators.ranking.CrowdingDistance;
import org.evosuite.kex.KexTestGenerator;
import org.evosuite.testcase.TestCase;
import org.evosuite.testcase.TestChromosome;
import org.evosuite.utils.LoggingUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Implementation of the DynaMOSA (Many Objective Sorting Algorithm) described in the paper
 * "Automated Test Case Generation as a Many-Objective Optimisation Problem with Dynamic Selection
 * of the Targets".
 *
 * @author Annibale Panichella, Fitsum M. Kifetew, Paolo Tonella
 */
public class DynaMOSA extends AbstractMOSA {

	private static final long serialVersionUID = 146182080947267628L;

	private static final Logger logger = LoggerFactory.getLogger(DynaMOSA.class);
	private static final Logger statLogger = LoggerFactory.getLogger("StatLogger");

	/** Manager to determine the test goals to consider at each generation */
	protected MultiCriteriaManager goalsManager = null;

	protected CrowdingDistance<TestChromosome> distance = new CrowdingDistance<>();

	private int stallLen;
	private int maxStallLen = 32;
	private boolean wasTargeted;
	private final int maxGenerateTests = 5;
	private final long kexExecutionTimeout = 5000;
	private final long kexGenerationTimeout = 5000;
	private KexTestGenerator kexTestGenerator;

	/**
	 * Constructor based on the abstract class {@link AbstractMOSA}.
	 *
	 * @param factory
	 */
	public DynaMOSA(ChromosomeFactory<TestChromosome> factory) {
		super(factory);
	}

	/** {@inheritDoc} */
	@Override
	protected void evolve() {
		List<TestChromosome> additional = Collections.emptyList();
		if (stallLen > maxStallLen) {
			logger.info("Run test generation using kex");
			stallLen = 0;
			wasTargeted = true;

			additional = new ArrayList<>();

			logger.info("Constraints collection");
			long startTime = System.currentTimeMillis();
			List<TestChromosome> solutions = getSolutions();
			statLogger.debug("Current solutions: {}", solutions.size());
//			statLogger.debug("-----------------------");
//			for (TestChromosome solution : solutions) {
//				statLogger.debug(solution.toString());
//				statLogger.debug("-----------------------");
//			}
			kexTestGenerator.collectTraces(
					solutions,
					() -> System.currentTimeMillis() - startTime > kexExecutionTimeout
			);
			long endExecutionTime = System.currentTimeMillis();

			logger.info("Start generation");
			Function0<Boolean> stoppingCondition =
					() -> System.currentTimeMillis() - endExecutionTime > kexGenerationTimeout;
			int i = 0;
			while (maxGenerateTests == -1 || i < maxGenerateTests) {
				TestCase testCase = kexTestGenerator.generateTest(stoppingCondition);
				if (testCase == null) {
					break;
				}
				TestChromosome test = new TestChromosome();
				test.setTestCase(testCase);
				additional.add(test);
				calculateFitness(test);
				logger.debug("Covered goals: {}", testCase.getCoveredGoals().size());
				i++;
			}
			long endTime = System.currentTimeMillis();
			statLogger.debug("Test cases generated: {}", additional.size());
//			statLogger.debug("---------------------");
//			for (TestChromosome test: additional) {
//				statLogger.debug(test.toString());
//				statLogger.debug("----------------------");
//			}

			statLogger.debug("Kex generation time: {}", endTime - endExecutionTime);
			statLogger.debug("Kex execution time: {}", endExecutionTime - startTime);
			statLogger.debug("Kex iteration time: {}", endTime - startTime);

			if (additional.isEmpty()) {
				return;
			}

			List<TestChromosome> temp = additional;
			additional = this.population;
			this.population = temp;
		}

		// Generate offspring, compute their fitness, update the archive and coverage goals.
		List<TestChromosome> offspringPopulation = this.breedNextGeneration();

		// Create the union of parents and offspring
		List<TestChromosome> union = new ArrayList<>(additional.size() + this.population.size() + offspringPopulation.size());
		union.addAll(additional);
		union.addAll(this.population);
		union.addAll(offspringPopulation);

		// Ranking the union
		logger.debug("Union Size = {}", union.size());

		// Ranking the union using the best rank algorithm (modified version of the non dominated
		// sorting algorithm)
		this.rankingFunction.computeRankingAssignment(union, this.goalsManager.getCurrentGoals());

		// let's form the next population using "preference sorting and non-dominated sorting" on the
		// updated set of goals
		int remain = Math.max(Properties.POPULATION, this.rankingFunction.getSubfront(0).size());
		int index = 0;
		this.population.clear();

		// Obtain the first front
		List<TestChromosome> front = this.rankingFunction.getSubfront(index);

		// Successively iterate through the fronts (starting with the first non-dominated front)
		// and insert their members into the population for the next generation. This is done until
		// all fronts have been processed or we hit a front that is too big to fit into the next
		// population as a whole.
		while ((remain > 0) && (remain >= front.size()) && !front.isEmpty()) {
			// Assign crowding distance to individuals
			this.distance.fastEpsilonDominanceAssignment(front, this.goalsManager.getCurrentGoals());

			// Add the individuals of this front
			this.population.addAll(front);

			// Decrement remain
			remain = remain - front.size();

			// Obtain the next front
			index++;
			if (remain > 0) {
				front = this.rankingFunction.getSubfront(index);
			}
		}

		// In case the population for the next generation has not been filled up completely yet,
		// we insert the best individuals from the current front (the one that was too big to fit
		// entirely) until there are no more free places left. To this end, and in an effort to
		// promote diversity, we consider those individuals with a higher crowding distance as
		// being better.
		if (remain > 0 && !front.isEmpty()) { // front contains individuals to insert
			this.distance.fastEpsilonDominanceAssignment(front, this.goalsManager.getCurrentGoals());
			front.sort(new OnlyCrowdingComparator<>());
			for (int k = 0; k < remain; k++) {
				this.population.add(front.get(k));
			}
		}

		this.currentIteration++;
		//logger.debug("N. fronts = {}", ranking.getNumberOfSubfronts());
		//logger.debug("1* front size = {}", ranking.getSubfront(0).size());
		logger.debug("Covered goals = {}", goalsManager.getCoveredGoals().size());
		logger.debug("Current goals = {}", goalsManager.getCurrentGoals().size());
		logger.debug("Uncovered goals = {}", goalsManager.getUncoveredGoals().size());
	}

	private long getLineCoverage() {
		return getCoveredGoals().stream().filter(it -> it instanceof LineCoverageTestFitness).count();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void generateSolution() {
		logger.debug("executing generateSolution function");

		// Set up the targets to cover, which are initially free of any control dependencies.
		// We are trying to optimize for multiple targets at the same time.
		this.goalsManager = new MultiCriteriaManager(this.fitnessFunctions);

		LoggingUtils.getEvoLogger().info("* Initial Number of Goals in DynaMOSA = " +
				this.goalsManager.getCurrentGoals().size() +" / "+ this.getUncoveredGoals().size());

		logger.debug("Initial Number of Goals = " + this.goalsManager.getCurrentGoals().size());

		if (this.population.isEmpty()) {
			// Initialize the population by creating solutions at random.
			this.initializePopulation();
		}

		// Compute the fitness for each population member, update the coverage information and the
		// set of goals to cover. Finally, update the archive.
		// this.calculateFitness(); // Not required, already done by this.initializePopulation();

		// Calculate dominance ranks and crowding distance. This is required to decide which
		// individuals should be used for mutation and crossover in the first iteration of the main
		// search loop.
		this.rankingFunction.computeRankingAssignment(this.population, this.goalsManager.getCurrentGoals());
		for (int i = 0; i < this.rankingFunction.getNumberOfSubfronts(); i++){
			this.distance.fastEpsilonDominanceAssignment(this.rankingFunction.getSubfront(i), this.goalsManager.getCurrentGoals());
		}

		// Evolve the population generation by generation until all gaols have been covered or the
		// search budget has been consumed.
		stallLen = 0;
		long startTime = System.currentTimeMillis();
		int iterations = 0;
		int kexIterations = 0;
		int kexImproveIterations = 0;
		kexTestGenerator = new KexTestGenerator();
		while (!isFinished() && getNumberOfUncoveredGoals() > 0) {
			wasTargeted = false;
			long oldCoverage = getLineCoverage();

			this.evolve();

			long newCoverage = getLineCoverage();
			long total = newCoverage + getUncoveredGoals().stream().filter(it -> it instanceof LineCoverageTestFitness).count();
			statLogger.debug("Coverage: {}/{}", newCoverage, total);
			statLogger.debug("Targeted: {}", wasTargeted);
			statLogger.debug("Time: {}", System.currentTimeMillis() - startTime);

			if (wasTargeted) {
				logger.debug("Old coverage: {}", oldCoverage);
				logger.debug("New coverage: {}", newCoverage);
				kexIterations++;
				if (oldCoverage < newCoverage) {
					statLogger.debug("Kex iteration improves coverage");
					kexImproveIterations++;
				} else {
					statLogger.debug("Dump kex iteration");
				}
			}

			if (oldCoverage == newCoverage) {
				if (wasTargeted) {
//					maxGenerateTests *= 2;
					maxStallLen *= 2;
				} else {
					stallLen++;
				}
			} else {
				stallLen = 0;
			}

			iterations++;
			this.notifyIteration();
		}
		long endTime = System.currentTimeMillis();

		statLogger.debug("Total iterations: {}", iterations);
		statLogger.debug("Total time: {}", endTime - startTime);
		statLogger.debug("Kex iterations: {}", kexIterations);
		statLogger.debug("Kex improve iterations: {}", kexImproveIterations);

		this.notifySearchFinished();
	}

	/**
	 * Calculates the fitness for the given individual. Also updates the list of targets to cover,
	 * as well as the population of best solutions in the archive.
	 *
	 * @param c the chromosome whose fitness to compute
	 */
	@Override
	protected void calculateFitness(TestChromosome c) {
		if (!isFinished()) {
			// this also updates the archive and the targets
			this.goalsManager.calculateFitness(c, this);
			this.notifyEvaluation(c);
		}
	}
}
