# zetaFunctionPoles
Implementation in Magma of an algorithm to calculate the stratification of $`\mu`$-constant plane branch deformations by the poles of the complex zeta function.

This is equivalent to the stratification by the roots of the Bernstein-Sato polynomial in the following cases:
- A plane branch deformation with pairwise different monodromy eigenvalues (this includes in particular the case of one characteristic exponent).
- A plane branch deformation for which the only coinciding candidates are of geometric origin (e.g. semigroup $`\langle 10,15,36 \rangle`$).

Plane branches can be considered as deformations with zero parameters, so this code can be used to calculate the set of poles (or the Bernstein-Sato polynomial in the previous cases) for a particular curve.

An article explaining the mathematical results in which the code is based will be published.

## Requirements
- Install [Magma](https://magma.maths.usyd.edu.au/magma/) (computer algebra system)
- Download [SingularitiesDim2/](https://github.com/rogolop/SingularitiesDim2) (library for plane curve singularities by Guillem Blanco)
- Download this repository

## Files
- `ZetaFunction/`: library for computing the stratification by the poles by the poles of the complex zeta function
- `usage/`: my personal usage of the library; you may ignore its contents; the correctness of the computed examples is not guaranteed
- `calculateExample.m`: simple script to compute examples
- `exampleOutput.txt`: output of `calculateExample.m`

## Usage example

See [calculateExample.m](calculateExample.m).


