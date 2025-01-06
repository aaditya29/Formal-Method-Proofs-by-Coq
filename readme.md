# Formal Method Proofs in Coq

## About This Repository

This repository is mainly about writing proofs of certified programs i.e. programs that come with a proof that it meets the desired specifications in `Coq`.<br>
A specification is a formal description of the behavior and properties that a program must satisfy. It defines what the program is supposed to do, often in terms of inputs, outputs, and the relationship between them.<br>
In `Coq` a specification is written using formal logic and mathematical expressions. The process involves writing both the program and its specification, and then using Coq's proof assistant capabilities to formally verify that the program meets the specification. This ensures a high level of confidence in the correctness of the program.<br>

**Please note that this repository is intended for educational purposes only.**<br>

### Installing Coq in VSCode on macOS

#### 1. Installing Homebrew on macOS

To install Homebrew on macOS, follow these steps:

1. Open the Terminal.
2. Paste the following command and press `Enter`:
   ```sh
   /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
   ```
3. Follow the on-screen instructions to complete the installation.

After the installation is complete, you can verify that Homebrew is installed by running:

```sh
brew --version
```

If any problem exists, visit the [Homebrew website](https://brew.sh/).

#### 2. Install `OPAM`

Opam is a package manager for OCaml that helps users install, upgrade, and manage OCaml compiler(s), tools, and libraries.<br>
To install `OPAM` type following in the Terminal:

```sh
brew install opam
```

#### 3. Installing `Coq` and VsCoq Language Server

To install Coq on MacOS through OPAM write the following commands in the Terminal:

1. Install Coq:

```sh
brew install coq
```

2. Install VSCoq Language Server

```sh
opam install vscoq-language-server
```

After installation, check that whether `vscoqtop` is installed by writing the following command:

```sh
which vscoqtop
```
