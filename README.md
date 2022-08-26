# WordleInIdris

"Wordle in Idris" is a project to demonstrate the power of type-constrained states for game logic. It is based on an example in chapter 14.3 of the book "Type Driven Development in Idris" by Edwin Brady. It follows the basic idea of the game wordle, as popularized by the New York Times, but with significantly fewer features. 

Possible extensions coming in the future:
- Web application to run game


## How to run it

Download Idris2 https://www.idris-lang.org/pages/download.html.

Add the Wordle folder into the idris2 folder. 

run terminal command ```idris2 -p contrib Wordle/Wordle.idr``` in idris2 folder.

## Why Idris

Idris is a functional programming language, similar to Haskell. If you do not know what functional programming languages are, I highly recommend you check them out. Instead of explaining all the basics, I will assume some knowledge of functional programming languages. 

Idris, in contrast with Haskell, uses dependent types. Rather, dependent types are built into the language whereas Haskell only has some attempts of implementation through external libraries. Dependent types are powerful, they are in essence functions that are types. The simplest example is the List type constructor. Notice how I used type constructor there because List *creates* a type. For example, List String is a type, List Int is a type, and List Bool is a type. However, List itself is not a type, but rather creates a type. To deconstruct this idea of List, think of it as the function Type -> Type. It takes a type, like String, Int, or even List String, and returns a new type, respectively: List String, List Int, List (List String). 

Another common example is the Vect family of types. A vector is a list with a predefined length. Take for instance Vect 4 String. This is a list of strings that is 4 elements long. This is also a type. Vect 5 String is a different type. A single natural number can change the type! In the same function idea as List, Vect has a type signature of Nat -> Type -> Type. Now the dependence can go all out! Imagine the arguments to the type, ie. what its dependent on, as storing information. Vect has more information than just List. Imagine how far this can be extended!

## States as Types

States in procedural or OOP languages take the form of a variable. It has a value, like a record, and is a global variable that any function can access and make changes to. However, in typed languages, states are not possible in the conventional sense. The way functional programming works is that changes can only be made through things that are inputted, as shown by the output. There aren't any variables, but simply potential outputs of a function. The logical proposition is to make states always input and output out of functions. For example, an indexer can carry around a state (the index it is on) while indexing a list. By recursively calling the indexer and passing along the state through the inputs, the list can be indexed without much hassle. However, there are some issues with this.

States simply being passed between functions only works when the function chain or recursion is linear. Problems arise with branched recursion, as seen simply with the indexing of a binary tree. Recursion splits off the indexing into the left and right branches, however, this means that whatever happens with the right branch is not conveyed to the left branch. The solution? States are outputted along with the output and get reassigned. For the binary tree, it is as simple as taking the output of the process of indexing the left side of the tree (which has the new state) and reapplying it while recursively labeling the left. This is tedious to do all the time, and so Idris and its dependent types come to the rescue.

Dependent types allow for the state to be defined as a monad. Now monads are a whole different topic, and to be discussed somewhere else. However, we can think of it right now as a sort of wrapper around some Type. If requested, they may give the type within the wrapper and an action can be performed on the inside type to change the whole monad itself. For example, List is a monad. List String wraps the String type within the List. On request, it can give the items inside the List to be dealt with. The most impactful part about monads is the bind function. Through this, many functions can be sequenced to allow for procedural-like programming. 

Anyways back to States. Now inside a monad container, the state can be *implicitly* transferred between functions, automatically accessible through the new State type, and thus reduces the clutter. States are automatically updated because of each successive function in the procedural like coding that monads allow require the output of the previous one. The value is passed around automatically, and when changed, would impact the ones afterward.

## States as Types in my Game

Okay, I rambled a lot about the mathy portion of states as types that probably didn't make sense because I tried to simplify it. Anyways, let's look at the application, and maybe even without the knowledge of how it works, you can appreciate its potential.

The state of the game is captured through the sum type: 
```
data GameState : Type where
   NotRunning : GameState
   Running : (guesses : Nat) -> (word : Word) -> (lastGuess : Word) -> GameState
 ```

This, simply put, states that the game could either be running or not running. If it is running, then with the state, contains the information on how many guesses are left, the word to guess, and the last guessed word. This is not the fancy monad thing I talked about earlier though. It is the basis of information about the state, similar to how records can contain various information about the state. The way states are handled is applied in the next type declaration:

```
data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
```
This is the 'command': bind, sequence, and pure are implemented for this type which makes it able to run for ```do```, the monadic powertool. Like how states should be managed, the first argument is any type. This represents the return type of an argument. Simplistically, states are managed by being returned alongside the return type of a function. For example, with the tree labeling state, the function must also return the labeled tree along with the state, which without dependent types is made through a pair of types. However, with our command type, the information can be stored within the type.

The second and third arguments show the magic. The first is a state, which is all good and well, however, confusion might arrive over the second: a function? Yes, it takes a function that takes the return type of the function (the first argument) and returns a state. For simplicity's sake, let's imagine right now that it is simply two states as the second and third arguments. These are the precondition and postcondition states. This essentially describes the way the states move with different commands. Actually, let's forgo the word 'describe' because it in reality **demands** that the state is exactly as the precondition before the command is run, and will exactly be the postcondition after the command is run. 

Let's look at the first command:
```
NewGame : (word : Word) -> GameCmd () NotRunning (const (Running 6 word NilWord))
```
When creating a new game, the state starts off as not running, then it becomes running. This means that a new game cannot be called when the game state is already running. This isn't the extent of the power of this, however.

```
Won : GameCmd () (Running guesses word word) (const NotRunning)
Lost : GameCmd () (Running 0 word lastGuess) (const NotRunning)
Guess : (guess : Word) -> GameCmd () (Running (S guesses) word lastGuess) (const (Running guesses word guess))
```
Here, I define when the game is won and when the game is lost. **As a type!** The type of winning is when the game state is ```Running guesses word word```. This basically means when the word that needs to be guessed is the same as the word that was last guessed. This is exactly the rule of the game, but it is not typed imperatively, but hard coded in the type signature of the function! The Lose constructor holds a similar effect. Losing can only happen when the amount of guesses reaches zero. Only then can the game be lost. Another rule, and yet again hard coded into the type signature. 

The postcondition type of the previous two constructors is NotRunning, because the game ends shortly after. Guess is the only action that changes the state from Running to Running. Here, we can see the rule of Guess in the type as well, where the only difference between the pre and post-conditions are the guesses. Successor guesses become guesses, meaning the postcondition has one less guess in it, and it also implies that the precondition has **more than one** guess. Beauty!

This is how types can define states within a game, and how the type can therefore describe the rules of the game through its type signature, without even any code! This ensures that a game follows the rules, or else it won't type check. There is plenty more to talk about here, but I'll leave it at that. If this has sparked any interest in learning type-driven programming or Idris for that matter, I highly recommend "Type Driven Development in Idris" by Edwin Brady.

Cheers,
Caleb






