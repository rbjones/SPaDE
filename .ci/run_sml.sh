#!/bin/sh
set -e

echo "Running ProofPower/PolyML conversion (container entrypoint)."

if command -v proofpower >/dev/null 2>&1; then
  echo "Using proofpower wrapper"
  if [ -f scripts/convert_theory.pp ]; then
    proofpower -batch -f scripts/convert_theory.pp
  else
    echo "scripts/convert_theory.pp not found; create it or edit this script."
    exit 1
  fi
elif command -v poly >/dev/null 2>&1 || command -v polyml >/dev/null 2>&1; then
  echo "Using PolyML"
  if [ -f scripts/convert_theory.sml ]; then
    poly -w /dev/null -l scripts/convert_theory.sml || true
  else
    echo "scripts/convert_theory.sml not found; create it or edit this script."
    exit 1
  fi
else
  echo "No ProofPower or PolyML binary found in PATH. Edit this script to match your container."
  exit 2
fi

mkdir -p out/sml
echo "SML conversion finished (placeholder)" > out/sml/result.txt
