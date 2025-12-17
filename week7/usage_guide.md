# Week 7: Automated Correctness Checking - Usage Guide

## Overview

This tool provides an automated verification pipeline that:
1. **Parses** Dafny programs to extract loop structure
2. **Synthesizes** linear invariants using Z3 constraint solving
3. **Inserts** synthesized (or provided) invariants into the program
4. **Verifies** the modified program using Dafny's built-in verification engine

## Installation

### Prerequisites
- Python 3.8+
- z3-solver: `pip install z3-solver`
- Dafny CLI installed and in PATH ([https://dafny.org](https://dafny.org))

### Verify Installation
```bash
# Check Dafny
dafny --version

# Check Z3 Python bindings
python3 -c "from z3 import *; print('Z3 OK')"
```

## Usage

### Basic Usage

```bash
# Insert invariants from JSON and verify
python3 verification_pipeline.py --input program.dfy --invariants invariants.json --output verified.dfy

# Auto-synthesize invariants and verify
python3 verification_pipeline.py --input program.dfy --output verified.dfy

# Just insert invariants without verification
python3 verification_pipeline.py --input program.dfy --invariants inv.json --output out.dfy --no-verify

# Output results as JSON
python3 verification_pipeline.py --input program.dfy --json-output
```

### Command Line Options

| Option | Short | Description |
|--------|-------|-------------|
| `--input` | `-i` | Input Dafny file (required) |
| `--output` | `-o` | Output file path for modified program |
| `--invariants` | `-inv` | JSON file containing invariants to insert |
| `--no-synthesize` | | Disable automatic invariant synthesis |
| `--no-verify` | | Skip Dafny verification step |
| `--dafny-path` | | Path to Dafny executable (default: `dafny`) |
| `--json-output` | | Output results as JSON |

## Invariants JSON Format

### Simple Format (Single Loop)
```json
{
  "invariants": [
    "0 <= i <= n + 1",
    "sum == i * (i - 1) / 2"
  ]
}
```

### Per-Loop Format (Multiple Loops)
```json
{
  "loops": [
    {
      "invariants": ["0 <= i <= n", "x >= 0"]
    },
    {
      "invariants": ["j >= i", "y == j * 2"]
    }
  ]
}
```

## Examples

### Example 1: Sum of Natural Numbers

**Input Program** (`sum.dfy`):
```dafny
method Sum(n: int) returns (result: int)
  requires n >= 0
  ensures result == n * (n + 1) / 2
{
  var i := 0;
  var sum := 0;
  
  while (i <= n)
  {
    sum := sum + i;
    i := i + 1;
  }
  
  result := sum;
}
```

**Invariants** (`sum_inv.json`):
```json
{
  "invariants": [
    "0 <= i <= n + 1",
    "sum == i * (i - 1) / 2"
  ]
}
```

**Run Pipeline**:
```bash
python3 verification_pipeline.py -i sum.dfy -inv sum_inv.json -o sum_verified.dfy
```

**Output**:
```
============================================================
Verification Pipeline Results
============================================================
Input: sum.dfy
Status: success

  Parsed method: Sum
  Found 1 loop(s)
  Loaded 2 invariant(s) from JSON
  Wrote output to: sum_verified.dfy
  ✓ Verification successful!

Verification Details:
  Verified: 2
  Errors: 0
============================================================
```

### Example 2: Auto-Synthesis Mode

```bash
python3 verification_pipeline.py -i counter.dfy -o counter_verified.dfy
```

The tool will automatically synthesize linear invariants using Z3 constraint solving.

## Programmatic API

You can also use the pipeline as a Python module:

```python
from verification_pipeline import VerificationPipeline, DafnyParser, InvariantInserter

# Create pipeline
pipeline = VerificationPipeline()

# Process a file
result = pipeline.process_file(
    input_path="program.dfy",
    output_path="verified.dfy",
    invariants_json_path="invariants.json",
    synthesize=True,
    verify=True
)

print(f"Status: {result['status']}")
print(f"Synthesized: {result['synthesized_invariants']}")
```

### Key Classes

| Class | Description |
|-------|-------------|
| `DafnyParser` | Parses Dafny programs and extracts structure |
| `InvariantInserter` | Inserts invariants at correct loop positions |
| `DafnyVerifier` | Executes Dafny verification and parses results |
| `LinearInvariantSynthesizer` | Synthesizes linear invariants using Z3 |
| `VerificationPipeline` | Orchestrates the complete workflow |

## Limitations

1. **Linear Invariants Only**: Auto-synthesis is limited to linear forms (`ax + by <= c`)
2. **Simple Loops**: Best results with simple integer arithmetic loops
3. **No Array Support**: Array invariants must be provided manually via JSON
4. **Single Method**: Currently processes one method at a time

## Troubleshooting

### Dafny Not Found
```
Error: Dafny not found at 'dafny'
```
**Solution**: Install Dafny and add to PATH, or use `--dafny-path /path/to/dafny`

### Z3 Not Available
```
Warning: Z3 not available. Cannot synthesize invariants.
```
**Solution**: Install z3-solver: `pip install z3-solver`

### Verification Failed
```
Status: verification_failed
```
**Solution**: Check the error messages - you may need to provide additional or different invariants

## File Structure

```
week7/
├── verification_pipeline.py   # Main pipeline implementation
├── usage_guide.md             # This documentation
├── README.md                  # Week 7 assignment overview
└── test_programs/             # Test Dafny programs
    ├── sum_no_invariants.dfy
    ├── sum_invariants.json
    ├── counter_no_invariants.dfy
    ├── counter_invariants.json
    ├── double_increment.dfy
    └── double_increment_invariants.json
```
