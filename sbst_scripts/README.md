# SBST Scripts

The aim of these scripts is statistics gathering and their further analysis. 

## Content description

- **run-experiment.py**

It's the entry point script. `-h` option will provide description of all options.

**Note:** It's important to run this script from `sbst_scripts` folder.

Usage example:
```bash
python run-experiment.py \
  --tool "~/tools/evokex" \
  --benchmarks "~/junitcontest/infrastructure/benchmarks_10th" \
  --csv "~/results/evokex.csv" \
  --output "~/output/evokex-output" \
  --runs 3 \
  --timeouts 30 60 120
```

- **run-experiment.sh** - Prepares environment
- **setup-and-run-docker.sh** - Creates and runs docker containers
- **run-and-collect.sh** - runs test generation on benchmarks and starts statistics computation
- **collect-coverage.sh** - runs jacoco for statistics computation
- **jars/** - contains all jars and loggers for jacoco coverage collection
- **gather_statistics.ipynb** - gathers statistics and builds some tables and plots

