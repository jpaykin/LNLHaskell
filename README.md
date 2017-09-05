# LNLHaskell

Linear types for Haskell in the style of Linear/Non-Linear logic.

This iteration of the code is accompanied by a paper in submission to ICFP 2017:
"The Linearity Monad"

------------------

This project uses [stack][] to provide a reproducible build system. To build the
project, make sure to install stack, and then run `stack setup` to install the
correct version of ghc and necessary packages in isolation. Next, run `stack
build` to compile the project or `stack ghci` to load the project in `ghci`. 

- `LNLHask.cabal` : cabal file, lists dependencies
- `stack.yaml` : stack configuration file, lists ghci version and extra
  dependencies 
- `src` : Haskell source code
  * `src/Prelim.hs` : preliminary data about type-level natural numbers,
    booleans, and lists
  * `src/Types.hs` : linear types
  * `src/Classes.hs` : type classes corresponding to the predicates about
    contexts 
  * `src/Interface.hs` : interface to linear terms using type classes
  * `src/DeepEmbedding.hs` : implementation of language as a deep embedding
  * `src/ShallowEmbedding.hs` : implementation of language as a shallow
    embedding 
  * `src/examples/` : implementation of domain-specific languages
    * `src/examples/Array.hs` : implementation of mutable functional arrays
    * `src/examples/FileHandles.hs` : implementation of functional file handles
	* `src/examples/LinTrans.hs` : linear algebra library for quantum computing
      example
	* `src/examples/Quantum.hs` : implementation of the quantum lambda calculus
	* `src/examples/Sessions.hs` : implementation of session types
	* `src/examples/ByteString.hs` : preliminary (work in progress)
      implementation of `ByteString`s


[stack]: www.haskellstack.org/


