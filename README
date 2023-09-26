# LieARTCharacters

Package that extends LieART for the use of 1-dimensional representations of Lie algebras, i.e. characters.
It is able to find the decomposition of 1-dim representations into characters of irreducible representations.


## Installation

The following function and commands will automatically download the latest release of LieARTCharacters (and LieART) and install it:

```mathematica
updateLieARTCharacters[] := Module[{json, entry, download, target},
  Check[json = Import["https://api.github.com/repos/jose-a-sa/LieARTCharacters/releases", "JSON"];
    entry = Last@SortBy[json, DateObject@*Lookup["published_at"]];
    download = Lookup[First@Lookup[entry, "assets"], "browser_download_url"];
    target = FileNameJoin[{CreateDirectory[], "LieARTCharacters.paclet"}];
    If[$Notebooks, PrintTemporary@Labeled[ProgressIndicator[Appearance -> "Necklace"], 
      "Downloading LieARTCharacters...", Right], Print["Downloading..."]];
    URLSave[download, target], Return[$Failed]
  ];
  If[FileExistsQ[target], PacletManager`PacletInstall[target, ForceVersionInstall->True], $Failed]
];
updateLieARTCharacters[]
Needs["LieARTCharacters`"]
```

## Usage

While using functions in this extension we need to specify the algebra we are working with. We use the same definitions of `Algebra` and `AlgebraClass` in LieART.
For example, `A2` or equivalently `Algebra[A][2]` is the complexified $\mathfrak{su}(3)$.

There's no need to install or load LieART before using the package. When using in Mathematica
```mathematica
<< LieARTCharacters`
```
the package will check for LieART among the installed packages, and will load it if found. Otherwise, it will automatically be downloaded from the [official website](https://lieart.hepforge.org/).
Once LieART is imported, LieARTCharacters modifies some of the internal definitions of LieART to better work with the product algebras, product irreps and product weights.

## Description

Many computations in the theoretical physics and field theory lead to large polynomial expressions that help count states and/or operators.
These states/operators are organized into the character semisimple representations of a Lie algebra $\mathfrak{g}$, i.e. as a formal sum of *irreps* (irreducible representations).
In terms of characters, this can be written as
$$\chi(z_1, \dots, z_r) = \sum_{\lambda\in I} m_{\lambda} \chi_{\lambda}(z_1, \dots, z_r) ~~.$$
Here we define:
- $\chi$ the full character and $\chi_{\lambda}$ the character of an irrep $R_{\lambda}$
- $r = \mathrm{rank}(\mathfrak{g})$ as the rank of the Lie algebra
- $\lambda$ is the Dinkin label that represents the highest weight of the representation $R_{\lambda}$
- $m_{\lambda} \in \mathbb{Z}$ is the multiplicity of the irrep $R_{\lambda}$

This package allows to compute characters of irreps of Lie algebras using the `WeightSystem` function from the LieART package.
Additionally, defines a weak ordering function to help sort dominant weights of irreps and obtain the highest weights in a expression.
Finally, and more importantly, `CharacterDecomposition[g][expr, {vars..}]` produces an `Association` encoding key-value pairs of $(\lambda, m_\lambda)$ for a given character $\chi$ of any semisimple representation of the algebra `g`.

## References

- Feger, R., Kephart, T. W., & Saskowski, R. J. (2019). LieART 2.0 -- A Mathematica Application for Lie Algebras and Representation Theory. ArXiv. https://doi.org/10.1016/j.cpc.2020.107490
- Fuchs Jürgen & Schweigert C. (1997). Symmetries lie algebras and representations : a graduate course for physicists. Cambridge University Press.
