# Chip-Firing with Lean4

This repository contains a complete formalization of the Riemann-Roch theorem for graphs. It includes the necessary background on chip-firing games on multigraphs, using the Lean 4 theorem prover and the Mathlib library. It loosely follows the terminology and organization of Chapters 1 through 6 of *Divisors and Sandpiles* by [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114). We hope that this library will serve as the starting point for the formalization of other topics, such as combinatorial Brill--Noether theory, that are build on the divisor theory of finite graphs.

Project documentation (including this project's docs and its Mathlib dependencies) is available at:
[Chip-Firing with Lean Documentation](https://dhyeymavani.com/chip-firing-with-lean/docs/ChipFiringWithLean/RiemannRochForGraphs.html)

- _Co-developed by **Dhyey Mavani** and **Nathan Pflueger**_

## Project Structure

This proof of Riemann--Roch is organized into the following files. Two additional files, ``CFGraphExample.lean`` and ``Algorithms.lean``, are independent material that are not dependencies for the main theorems.

```text
┌────────────────────────────────────────────────────────────────────────┐
│ Basic.lean                                                             │
│ Divisor groups, winnability,                                           │
│ q-reducedness                                                          │
└────────────────┬──────────────────────────────────────┬────────────────┘
                 │                                      │
┌────────────────┴────────────────┐    ┌────────────────┴────────────────┐
│ Config.lean                     │    │ Rank.lean                       │
│ Configurations, superstability, │    │ Baker-Norine ranks              │
│ Dhar's algorithm                │    │                                 │
└────────────────┬────────────────┘    └────────────────┬────────────────┘
                 │                                      │
┌────────────────┴────────────────┐                     │
│ Orientation.lean                │                     │
│ Orientations, consequences      │                     │
│ for superstability              │                     │
└────────────────┬────────────────┘                     │
                 │                                      │
┌────────────────┴──────────────────────────────────────┴────────────────┐
│ RRGHelpers.lean                                                        │
│ Helper results for Riemann-Roch                                        │
└───────────────────────────────────┬────────────────────────────────────┘
                                    │
┌───────────────────────────────────┴────────────────────────────────────┐
│ RiemannRochForGraphs.lean                                              │
│ Proof of Riemann-Roch theorem and corollaries; gonality                │
└────────────────────────────────────────────────────────────────────────┘
```

## Installation

1. **Install Lean 4 and Lake**:
   Follow the [Lean 4 installation guide](https://lean-lang.org/install/).

2. **Clone the Repository**:
   ```bash
   git clone https://github.com/DhyeyMavani2003/chip-firing-with-lean.git
   cd chip-firing-with-lean
   ```

3. **Build the Project**:
   Use the Lake build tool to compile and set up dependencies.
   ```bash
   lake exe cache get
   lake build
   ```

For futher information about working with Lean4/Mathlib projects, consult the [Mathlib project guide](https://leanprover-community.github.io/install/project.html).

### Contact
For questions, contributions, or collaboration, please reach out to [Dhyey Mavani](mailto:ddmavani2003@gmail.com) and [Nathan Pflueger](mailto:npflueger@amherst.edu).
