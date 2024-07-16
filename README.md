Lambdapi library for Zenon
==========================

[Lambdapi](https://github.com/Deducteam/lambdapi) library used by the
automated theorem prover
[ZenonModulo](https://github.com/Deducteam/zenon_modulo/tree/modulo)
for generating Lambdapi proofs.

Installation with Opam
----------------------

```
opam repository -a add lambdapi https://github.com/deducteam/opam-lambdapi-repository.git # once
opam install lambdapi-zenon
```

Usage in Lambdapi
-----------------

```
require open Stdlib.Prop Stdlib.Set Stdlib.Eq Stdlib.FOL Logic.Zenon.Main;
```

Compilation from the sources
----------------------------

```
opam install --deps-only . # once
make
```

Installation from the sources
-----------------------------

```
opam install .
```
