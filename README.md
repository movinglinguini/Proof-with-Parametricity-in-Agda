# Proving a mystery function is actually the ID function with Parametricity in Agda

What a mouthful.

This development was done as part of a final project for Dr. Chris Martens's [Intensive Principles of Programming Languages](https://www.khoury.northeastern.edu/home/cmartens/Courses/7400-f24/index.html) course in Fall 2024.
It illustrates how to perform a small proof using a parametricity theorem.

## Structure of the project

- `SystemF.agda` encodes a fragment of System F with polymorphic types and expressions.
- `Parametricity.agda` contains equivalence rules, the parametricity theorem (postulated--no proof), and the theorem we want to prove.
- `LFT.agda` was made to experiment with the Lightweight Free Theorems package for Agda. See [the package page on the wiki](https://wiki.portal.chalmers.se/agda/agda.php?n=Libraries.LightweightFreeTheorems) for instructions on how to use that.
- `Zine.agda` is the zine I made for explaining the code (part of the project requirements) in printable format.
- `Zine-Book.agda` is the same zine but in PDF book format, so you can read through it easily on GitHub without download.
