# Towards Step-wise explanations of Complex Search Trees

This repository contains the code to reproduce the results of the following paper:

> **Towards Step-wise explanations of Complex Search Trees**  
> Ignace Bleukx, Peter J. Stuckey, Tias Guns  
> *CP 2026 (to appear)*

Modern constraint solvers solve combinatorial problems through search with branching, propagation, and nogood learning. Although effective, the resulting search trees are hard to interpret: many branches and low-level inferences obscure why a conclusion is reached. Step-wise explanations provide an inference-based alternative, but prior successes were mainly for puzzle-style problems that required little or no search when solved by a CP-solver.
We investigate whether step-wise explanations can be extended to search-heavy combinatorial problems. 
We study explanation sequences with only user-level constraints, ideally just one per step, and construct them from solver proof logs through nested explanations of complex steps. 
Our results indicate that concise user-level explanations are often achievable, even when solving requires many search nodes, while also highlighting open challenges such as deep nesting in some instances and dependence on proof generation. 
This motivates future work on explanation-aware solving and richer explanation languages.

This work builds upon [Proof2Seq](https://github.com/ML-KULeuven/Proof2Seq), published at AAAI'25, which converts solver proofs into step-wise explanations for propagation-heavy problems.


## Installation

### Prerequisites

- **Python** 3.8 or newer
- **Rust** stable toolchain ([install via rustup](https://www.rust-lang.org/tools/install))
- **Git** (with submodule support)
- A C compiler (required by `maturin` to build the Pumpkin Python bindings)

### Setup

Clone the repository with submodules and install all dependencies:

```bash
git clone --recurse-submodules https://github.com/ML-KULeuven/Stepwise-ComplexSearch.git
cd Stepwise-ComplexSearch
make install
```

`make install` does the following:

1. Installs Python dependencies from `requirements.txt`
2. Installs a pinned [CPMpy](https://github.com/CPMpy/cpmpy) commit (13dec1a)
3. Builds the `pumpkin-solver` Python package from the `pumpkin/` submodule (skipped if already installed)

If you already cloned without submodules:

```bash
git submodule update --init --recursive
make install
```

To force a rebuild of Pumpkin (e.g. after pulling submodule changes):

```bash
make reinstall-pumpkin
```

> **Note:** The `exact` solver does not build on macOS, [install from source instead](https://gitlab.com/nonfiction-software/exact)


## Codebase layout

```
Stepwise-ComplexSearch/
├── example.py                    # Minimal job-shop example
├── experiments.py                # Run benchmark experiments and download PSPLib data
├── nested_explanations.py        # Nested explanation algorithm (main entry point)
├── utils.py                      # Domain shrinking and lexicographic MUS helpers
├── benchmarks/                   # Benchmark instances
├── proof2seq/                    # Proof-to-sequence pipeline (from AAAI'25 [Proof2Seq](https://ojs.aaai.org/index.php/AAAI/article/view/38432/42394))
│   ├── parsing.py                # DRCP proof parser for Pumpkin proofs
│   ├── pipeline.py               # End-to-end proof → explanation sequence pipeline
│   ├── simplify.py               # Proof simplification
│   ├── minimize.py               # Proof trimming and minimization
│   ├── mus.py                    # MUS algorithms (deletion-based, SMUS)
│   └── utils.py                  # Proof/sequence printing and statistics
```

**Workflow.** A CPMpy model is solved with Pumpkin to obtain a DRCP proof (`proof2seq/pipeline.py`). The proof is parsed, simplified, and converted into a flat explanation sequence (`proof2seq/`). Steps that use more than one user-level constraint are then recursively explained via `nested_explanations.py`, producing a nested explanation sequence.


## Running the code

The included example models a small job-shop scheduling problem and computes a nested explanation sequence for its unsatisfiability:

```bash
python example.py
```

To explain your own model, call `find_explanation_sequence` from `nested_explanations.py`:

```python
import cpmpy as cp
from nested_explanations import find_explanation_sequence

model = cp.Model(...)  # must be UNSAT
sequence, proof = find_explanation_sequence(model)
```

## Benchmark experiments

Paper benchmark results can be reproduced with the Makefile targets below. Each target runs `experiments.py` on every instance in the corresponding dataset and writes JSON statistics to `results/<benchmark>/`.

| Target | Dataset | Output directory |
|---|---|---|
| `make nurserostering` | Nurse rostering instances in `benchmarks/nr_musses/`, based of [schedulingbenchmarks.org](https://www.schedulingbenchmarks.org) | `results/nurserostering/` |
| `make rcpsp` | RCPSP instances from [PSPLib](https://www.om-db.wi.tum.de/psplib/) (j30, j60, j90, j120) | `results/rcpsp/` |

```bash
make nurserostering
make rcpsp
```

`make rcpsp` first downloads any missing PSPLib families via `experiments.py --download-psplib`. You can also download the RCPSP data separately:

```bash
python experiments.py --download-psplib
```

To run a single instance:

```bash
python experiments.py --model benchmarks/nr_musses/instance_1_1.pickle
python experiments.py --family j30 --instance j301_1
```

## Citation

If you use this code, please cite:

```bibtex
@inproceedings{bleukx2026towards,
  author    = {Ignace Bleukx and Peter J. Stuckey and Tias Guns},
  title     = {Towards Step-wise explanations of Complex Search Trees},
  booktitle    = {{CP}},
  series       = {LIPIcs},
  publisher    = {Schloss Dagstuhl - Leibniz-Zentrum f{\"{u}}r Informatik},
  year         = {2026}
  note         = {to appear}
}
```
