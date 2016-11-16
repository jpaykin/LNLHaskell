# LNLHaskell

Linear types for haskell in the style of Linear/Non-Linear logic

Author: Jennifer Paykin (jpaykin)

------------------

This project uses [stack][] to provide a reproducible build system. To build the
project, make sure to install stack, and then run `stack setup` to install the
correct version of ghc and necessary packages in isolation. Next, run `stack
build` to compile the project or `stack ghci` to load the project in `ghci`. 

- `LNLHask.cabal` : cabal file, lists dependencies
- `stack.yaml` : stack configuration file, lists ghci version and extra
  dependencies 
- `src` : Haskell source code
  * `src/Types.hs` : linear types
  * `src/Context.hs` : singleton types describing predicates about contexts
  * `src/Proofs.hs` : proofs about the predicates in `Context.hs`
  * `src/Classes.hs` : type classes corresponding to the predicates about
    contexts 
  * `src/Lang.hs` : data structure representing linear terms
  * `src/Subst.hs` : substitution and evaluation functions
  * `src/Interface.hs` : interface to linear terms using type classes
  * `src/Examples.hs` : example linear terms


[stack]: www.haskellstack.org/


