#!/bin/bash

# Navigate to the project root (adjust if needed)
#cd "$(dirname "$0")"

# Run all Python unittests found in the tests/ directory
#echo "🔍 Discovering and running all unit tests in ./tests"
python3 -m unittest discover -s tests -p "test_*.py" -v
