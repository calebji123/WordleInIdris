# WordleInIdris

"Wordle in Idris" is a project to demonstrate the power of type constrained states for game logic. It is based on an example in chapter 14.3 of the book "Type Driven Development in Idris" by Edwin Brady. It follows the basic idea of the game wordle, as popularized by the New York Times, however with significantly fewer features. 

Possible extensions coming in the future:
- Randomized words
- Infinite replayability
- Check for valid words
- Web application to run game


## Why Idris

Idris is a functional programming language, similar to Haskell. If you do not know what functional programming languages are, I highly reccomend you to check them out. In lieu of explaining all the basics, I will assume some knowledge of functional programming languages. 

Idris, in contrast with Haskell, uses dependent types. Rather, dependent types are built into the language whereas Haskell only has some attempts of implementation through external libraries. Dependent types are powerful, they are in essence functions that are types. The simplest example is the List type constructor. Notice how I used type constructor there, because List *creates* a type. For example: List String is a type, List Int is a type, List Bool is a type. However, List itself is not a type, but rather creates a type. To deconstruct this idea of List, think of it as the function Type -> Type. It takes a type, like String, Int, or even List String, and returns a new type, respectively: List String, List Int, List (List String). 

Another common example is the Vect family of types. A vector is a list with a predefined length. Take for instance Vect 4 String. This is a list of strings that is 4 elements long. This is also a type. Vect 5 String is a different type. A single natural number can change the type! In the same function idea as List, Vect has a type signature of Nat -> Type -> Type. Now the dependence can really go all out! Imagine the arguements to the type, ie. what its dependent on, as storing information. Vect has more information than just List. Imagine how far this can be extended!

## States as Types

States in a procedural or OOP language takes the form of a variable. It has a value, like a record, and is a global variable that any function can access and make changes to. However, in typed languages, states are not possible in the conventional sense. The way functional programming works is that changes can only be made through things that are inputted, as shown by the output. There aren't any variables, but simply potential outputs of a function. The logical proposition is to make states always input and output out of functions. For example, and an indexer can carry around a state (the index it is on) while indexing a list. By recursively calling the indexer and passing along the state through the inputs, the list can be indexed without much hassle. However, there are some issues with this.

States simply being passed between functions only works when the function chain or recursion is linear. Problems arise with branched recursion, as seen simply with the indexing of a binary tree. Recursion splits off the indexing into the left and right branches, however this means that whatever happens with the right branch is not conveyed to the left branch. The solution? States are outputted along with the output and get reassigned. For the binary tree, it is as simple as taking the output of the process of indexing the left side of the tree (which has the new state) and reapplying it while recursively labelling the left. This is tedious to do all the time, and so Idris and its dependent types come to the rescue.

Dependent types allow for the state to be defined as a monad. Now monads are a whole different topic, and to be discussed somewhere else. However, we can think of it right now as a sort of wrapper around some Type. If requested, they may give the type within the wrapper and an action can be performed on the inside type to change the whole monad itself. For example List is a monad. List String wraps the String type within the List. On request, it can give the items inside the List to be dealt with. The most impactful part about monads is through the bind function. Basically many functions can be sequenced that allow for procedural-like programming. 

Anyways back to States. Now inside a monad container, the state can be *implicitly* transferred between functions, automatically accessible through the new State type, and thus reduces the clutter. States are automatically updated, because each successive function in the procedural like coding that monads allow require the output of the previous one. The value is passed around automatically, and when changed, would impact the ones afterward.

# States as Types in my Game

Okay I rambled a lot about the mathy portion of states as types that probably didn't make sense because I tried to simplify it. Anyways, let's look at the application and maybe even without the knowledge of how it works, you can appreciate its potential.

The state of the game is captured through the sum type: 
'''
data GameState : Type where
   NotRunning : GameState
   Running : (guesses : Nat) -> (word : Word) -> (lastGuess : Word) -> GameState
 '''

This, simply put, states that the game could either be running or not running. If it is running, then with the state, contains the information on how many guesses is left, the word to guess and the last guessed word. This is not the fancy monad thing I talked about earlier though. It is the basis of information about the state, similar to how records can contain various information about the state. The way states are handled is applied in the next type declaration:









