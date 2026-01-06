# Chip-Firing with Lean4

A formalization of chip-firing games and the Riemann-Roch theorem for graphs using the Lean 4 theorem prover.

## Overview

This project provides a formal mathematical framework for studying **chip-firing games on graphs** and proves key results, including the **Riemann-Roch theorem for graphs**. The implementation leverages Lean 4 for formal proofs and structured reasoning.

The codebase is modular, with the following key components:

- **`Basic`**: Core definitions and utilities for `CFGraph` and structures related to divisors, including the existence and uniqueness of q-reduced divisors.
- **`CFGraphExample`**: Example graphs and chip-firing scenarios to verify functionality.
- **`Config`**: Definitions and operations involving configurations on `CFGraph`s.
- **`Orientation`**: Definitions and utilities for orientations on `CFGraph`s.
- **`Rank`**: Rank functions and related structures for divisors.
- **`RRGHelpers`**: Specific lemmas and results used in proving the **Riemann-Roch theorem**.
- **`RiemannRochForGraphs`**: The **main** formalization of the Riemann-Roch theorem for graphs.

## Requirements

To run and explore the project, you will need the following:

- **Lean 4**
- **Lake**: Lean 4's build tool
- Required dependencies (managed via `lakefile.lean`):
  - [mathlib4](https://github.com/leanprover-community/mathlib4): Core mathematical library for Lean 4
  - **Paperproof**: (Optional) proof visualization tool

## Project Structure

```
.
├── ChipFiringWithLean/
│   ├── Basic.lean              # Core chip-firing definitions
│   ├── CFGraphExample.lean     # Example graphs and configurations
│   ├── Config.lean             # Configuration-related structures
│   ├── Orientation.lean        # Orientation-related structures
│   ├── Rank.lean               # Rank of divisors definitions
│   ├── RRGHelpers.lean         # Helper results for Riemann-Roch
│   └── RiemannRochForGraphs.lean # Formal proof of Riemann-Roch theorem
├── lakefile.lean               # Build and dependency management
└── README.md                   # Project documentation
```

## Features

- **Graph Formalization**: Provides formal definitions of graphs and chip configurations.
- **Chip-Firing Mechanics**: Models chip-firing moves and associated game rules.
- **Example Scenarios**: Includes concrete examples for validation and testing.
- **Riemann-Roch Theorem**: Formalizes and proves the Riemann-Roch theorem for graphs.
- **Helper Libraries**: Offers reusable lemmas and tools for related graph-theoretical work.
- **Visualization**: Optional integration with Paperproof for better visualization of proofs.

## Installation

1. **Install Lean 4 and Lake**:
   Follow the [Lean 4 installation guide](https://leanprover.github.io/lean4/doc/setup.html).

2. **Clone the Repository**:
   ```bash
   git clone https://github.com/yourusername/chip-firing-with-lean.git
   cd chip-firing-with-lean
   ```

3. **Build the Project**:
   Use the Lake build tool to compile and set up dependencies.
   ```bash
   lake exe cache get
   lake build
   ```

## Development Workflow

- Build the project:
  ```bash
  lake build
  ```
- Clean build artifacts:
  ```bash
  lake clean
  ```
- Open Lean files in an IDE like VS Code (recommended with Lean 4 extension).

## Contributing

Contributions are highly welcome! Here are a few ways to contribute:

1. **Bug Fixes**: Submit pull requests for any bugs or issues you identify.
2. **New Features**: Add modules, lemmas, or optimizations related to chip-firing or graph theory.
3. **Documentation**: Improve clarity, examples, or explanations in the documentation.
4. **Testing**: Add more example graphs or scenarios to test edge cases.

Please ensure your contributions follow best practices and include detailed comments.

## License

This project is licensed under the [MIT License](LICENSE).

## References

### Software
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)

### Papers
- M. Baker and S. Norine, *Riemann-Roch and Abel-Jacobi theory on a finite graph*, Advances in Mathematics, 215 (2007), 766–788.
- S. Corry and D. Perkinson, *Divisors and Sandpiles: An Introduction to Chip-Firing*, American Mathematical Society, Providence, Rhode Island. 2018.
- R. Wang, J. Zhang, Y. Jia, R. Pan, S. Diao, R. Pi, and T. Zhang, *TheoremLlama: Transforming General-Purpose LLMs into Lean4 Experts*, arXiv preprint, https://arxiv.org/abs/2407.03203, 2024.
- V. Kiss and L. Tóthmérész, *Chip-firing games on Eulerian digraphs and NP-hardness of computing the rank of a divisor on a graph*, Discrete Applied Mathematics, vol. 193, pp. 48–56, Oct. 2015. DOI: http://dx.doi.org/10.1016/j.dam.2015.04.030.

### Article & Blog Links
- [Terence Tao AMS Post on Machine Assisted Proofs](https://www.ams.org/journals/notices/202501/noti3041/noti3041.html?adat=January%202025&trk=3041&pdfissue=202501&pdffile=rnoti-p6.pdf&cat=none&type=.html&utm_source=Informz&utm_medium=email&utm_campaign=Informz%20Mailing&_zs=x9GnR1&_zl=7A3f7)

---

### Acknowledgments

I would like to express my deepest gratitude to **Professor Nathan Pflueger**, my mathematics thesis advisor at Amherst College, for his invaluable guidance, support, and encouragement throughout this project.

---

### Contact
For questions, contributions, or collaboration, please reach out to [Dhyey Mavani](mailto:ddmavani2003@gmail.com).

---

Happy proving! 🚀