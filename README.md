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
  * `src/Frame.hs` : singleton types describing predicates about contexts
  * `src/FrameClass.hs` : type classes corresponding to the predicates about
    contexts 
  * `src/Lang.hs` : data structure representing linear terms
  * `src/Interface.hs` : interface to linear terms using type classes
  * `src/Examples.hs` : example linear terms


[stack]: www.haskellstack.org/

----------------------

# To Do

The linear sub-language is represented as an indexed data type (defined in Lang)
that uses predicates (defined in Frame) to describe the contexts of free linear
variables for each term. These expressions are hard to work with, and I envision
two levels of making linear terms easier to deal with. First, we define type
classes that characterize the predicates about contexts (FrameClass) and an
interface to linear expressions that refers to these type classes (Interface).
This forces Haskell to search for the proofs of these predicates instead of
making the user supply them. However, this type class interface is still not
perfect as it requires concrete variables represented as Nats and annotations
about all the variables used in an entire term. Therefore, the second layer of
convenient interface (yet to be attempted) will be a Template Haskell pass that
converts some nice linear code to the annotated type-class interface.

The following things still need to be done:

1) Define the substitution and evaluation functions in Lang.hs. This is going to
depend on a lot of lemmas about the predicates in Frame, which are going to be
annoying to prove. 

2) Add the Template Haskell layer and come up with syntax/a good top-level
interface for the language. This step will involve coming up with fresh
identifiers, good error messages, etc. and writing some kind of checker.

3) Type inference in the Template Haskell layer, to minimize the type
annotations needed?

4) Add user-defined linear data types. The first step of this may be to manually
add units, products, sums, etc, but ideally I would like users to specify their
own linear data types. Other considerations include the ability to use a data
structure either linearly (if the data is linear) or non-linearly if the data is
non-linear.

