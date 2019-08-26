HomuSat: A Type-Based HFL Model Checker
=======================================

**HomuSat** is a fully-automated tool for **HFL model checking**. HFL model checking is the problem of deciding whether a given finite-state labeled transition system (LTS) satisfies a given formula of higher-order modal fixpoint logic (HFL).

## Requirements

OCaml version >= 4.04.0

## Usage

For compilation, just type:

    $ make

[OCamlMakefile](http://mmottl.github.io/ocaml-makefile/) (included) will hopefully take care of everything needed.

Execution with a specific input file can be done by either of the commands below:

    $ ./homusat < [filename]
    $ ./homusat -f [filename]

## Input File Format

Below is an example input file:

    %HES
    S =_\nu <a>(F (<b>S));
    F =_\mu \lambda X. X \lor <c>S \lor <a>(F (<b>X));

    %LTS
    initial state: q0
    transitions:
    q0 c -> q0.
    q0 a -> q1.
    q1 b -> q2.
    q2 a -> q0.

In an input file, please specify an HFL formula that expresses the property you want to check in the form of an **HES** under the label `%HES`. An HES is expressed as a sequence of fixpoint equations separated by `;`. A fixpoint equation is an equation of the form `F =_x φ`, where `F` is a left-hand side variable, `x` is a fixpoint operator (either `\mu` or `\nu`), and `φ` is an HFL formula. To specify a right-hand side formula `φ`, you can use variables (a sequence of alphabets), constants (`\true` and `\false`), logical connectives (`\lor` and `\land`), modal operators (`<a>φ` and `[a]φ`), and lambda abstractions (`\lambda X.φ`).
An LTS is specified under the label `%LTS` by an initial state and a (possibly empty) sequence of transitions. Transitions should be separated by periods. Each transition `p a -> q` expresses that there is an edge from the state `p` to the state `q` with the label (action) `a`.
You can write comments in C-style (that is, in the form of either `//...` or `/*...*/`).

You can find various input files under the directory [`bench`](/bench). The benchmark problems used in the experiments in our APLAS 2019 paper are found in [`bench/exp`](/bench/exp).

## Options

- `-v [n]`: set verbosity level to `n` (default value is `0`)

- `-f [s]`: set input file name to `s` (stdin is used by default)

- `-t [f]`: set time-out to `f` seconds (default value is `10.0`)

- `-l [n]`: set maximum loop count to `n` (default value is `1,000,000`)

- `-d`: enable debug mode (give each variable a unique display name)

## Latest Version

See the [main developer's fork](https://github.com/aicabod/homusat) for the latest (but possibly unstable) version.
