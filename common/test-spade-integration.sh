#!/bin/bash

# test-spade-integration.sh - Test SPaDE integration with ProofPower HOL
# This script can be run inside the ProofPower container to test SPaDE scraping functionality

set -e

echo "Starting SPaDE integration tests..."

# Source ProofPower environment
if [ -f "$PPDIR/dev_env" ]; then
    source "$PPDIR/dev_env"
    echo "✓ ProofPower environment loaded"
else
    echo "✗ ProofPower environment not found at $PPDIR/dev_env"
    exit 1
fi

# Test that HOL is accessible
echo "Testing HOL accessibility..."
if command -v pp >/dev/null 2>&1; then
    echo "✓ pp command available"
else
    echo "✗ pp command not found"
    exit 1
fi

# Test HOL database access
echo "Testing HOL database access..."
pp -d hol <<EOF || {
    echo "✗ Failed to access HOL database"
    exit 1
}
get_theory "basic_hol";
quit();
EOF
echo "✓ HOL database accessible"

# Test theory hierarchy enumeration
echo "Testing theory hierarchy enumeration..."
pp -d hol <<EOF || {
    echo "✗ Failed to enumerate theories"
    exit 1
}
map (fn thy => (thy, get_parents thy)) (get_theories());
quit();
EOF
echo "✓ Theory hierarchy enumeration successful"

# Add your SPaDE-specific tests here
echo "Running SPaDE scraper tests..."

# Example test structure:
# if [ -f "spade_scraper.py" ]; then
#     python3 spade_scraper.py --test
#     echo "✓ SPaDE scraper tests passed"
# else
#     echo "⚠ SPaDE scraper not found, skipping tests"
# fi

echo "All tests completed successfully!"