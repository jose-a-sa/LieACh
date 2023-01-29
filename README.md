# LieARTCharacters

Single file package that extends LieART for the use of 1-dimensional representations of Lie algebras, i.e. characters.

## Description

Many computations in the theoretical physics and field theory lead to large polynomial expressions that help count states and/or operators.
These states/operators are organized into the character semisimple representations of a Lie algebra $\mathfrak{g}$, i.e. as a formal sum of *irreps* (irreducible representations).
In terms of characters, this can be written as
$$\chi(z_1, \dots, z_r) = \sum_{\lambda\in I} m_{\lambda} \chi_{\lambda}(z_1, \dots, z_r) ~~.$$
Here we define:
- $\chi$ the full character and $\chi_{\lambda}$ the character of an irrep $R_{\lambda}$;
- $r = \mathrm{rank}(\mathfrak{g})$ as the rank of the Lie algebra;
- $\lambda$ is the Dinkin label that represents the highest weight of the representation $R_{\lambda}$;
- $m_{\lambda}\in\mathbb{Z}_{+}$ is the multiplicity of the irrep $R_{\lambda}$.

This package allows to compute characters of irreps of Lie algebras using the `WeightSystem` function from the LieART package.
Additionally, defines an weak ordering function to help sort dominant weights of irreps and obtain the highest weights in a expression.
Finally, and more importantly, `CharacterDecomposition[g][expr, {vars..}]` produces an `Association` encoding key-value pairs of $(\lambda, m_\lambda)$ given a character $\chi$ of any semisimple representation of an algebra `g`.

## Usage

While using functions in this extension we need to specify the algebra we are working with. We use the same definitions of `Algebra` and `AlgebraClass` in LieART.
For example, `A2` or equivalently `Algebra[A][2]` is the complexified $\mathfrak{su}(3)$.

There's no need to install or load LieART before using the package. When using in Mathematica
```mathematica
<< LieARTCharacters`
```
the package will check for LieART among the installed packages and will load it if it present. Otherwise, it will automatically download it from the [official website](https://lieart.hepforge.org/).

Once it is downloaded and imported, it modifies some of the internal definitions of LieART to better work with the product algebras, product irreps and product weights.

## References

- Feger, R., Kephart, T. W., & Saskowski, R. J. (2019). LieART 2.0 -- A Mathematica Application for Lie Algebras and Representation Theory. ArXiv. https://doi.org/10.1016/j.cpc.2020.107490
- Fuchs Jürgen & Schweigert C. (1997). Symmetries lie algebras and representations : a graduate course for physicists. Cambridge University Press.