import Data.Vect
import Data.Vect.Elem
import Decidable.Equality
import Data.String
import System.File
import System.File.ReadWrite

%default total

data Word = NilWord | OKWord (Vect 5 Char)

vectToList : Vect n Char -> List Char
vectToList [] = []
vectToList (x :: xs) = x :: vectToList xs

Show Word where
   show NilWord = ""
   show (OKWord xs) = pack (vectToList xs)

testWord : Word
testWord = OKWord $ fromList $ map toLower ['h', 'e', 'l', 'l', 'o']

inMakesOut : (xs = ys -> Void) -> OKWord xs = OKWord ys -> Void
inMakesOut f Refl = f Refl

NilNotOK : NilWord = OKWord xs -> Void
NilNotOK Refl impossible

OKNotNil : OKWord xs = NilWord -> Void
OKNotNil Refl impossible

DecEq Word where
   decEq NilWord NilWord = Yes Refl
   decEq (OKWord xs) (OKWord ys) = case decEq xs ys of
                                        (Yes Refl) => Yes Refl
                                        (No contra) => No (inMakesOut contra)
   decEq NilWord (OKWord xs) = No NilNotOK
   decEq (OKWord xs) NilWord = No OKNotNil


data GameState : Type where
   NotRunning : GameState
   Running : (guesses : Nat) -> (word : Word) -> (lastGuess : Word) -> GameState


data GuessResult = Correct | Incorrect


data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
   NewGame : (word : Word) -> GameCmd () NotRunning (const (Running 6 word NilWord))

   Won : GameCmd () (Running guesses word word) (const NotRunning)
   Lost : GameCmd () (Running 0 word lastGuess) (const NotRunning)

   Guess : (guess : Word) -> GameCmd () (Running (S guesses) word lastGuess) (const (Running guesses word guess))
   
   ShowState : GameCmd () state (const state)
   Message : String -> GameCmd () state (const state)
   ReadGuess : GameCmd Word state (const state)

   Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
   (>>=) : GameCmd a state1 state2_fn
            -> ((res : a) -> GameCmd b (state2_fn res) state3_fn) 
            -> GameCmd b state1 state3_fn

(>>) : GameCmd () state1 state2_fn 
         -> Lazy (GameCmd a (state2_fn ()) state3_fn)
         -> GameCmd a state1 state3_fn


namespace Loop
   public export
   data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
      (>>=) : GameCmd a state1 state2_fn 
               -> ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn))
               -> GameLoop b state1 state3_fn
      (>>) : GameCmd () state1 state2_fn ->
           Inf (GameLoop a (state2_fn ()) state3_fn) ->
           GameLoop a state1 state3_fn
      Exit : GameLoop () NotRunning (const NotRunning)


gameLoop : {guesses : _} -> {word : _} -> 
               GameLoop () (Running (S guesses) word lastGuess) (const NotRunning)
gameLoop {guesses} {word} = 
   do ShowState
      Message "\nMake a guess to continue"
      g <- ReadGuess
      Guess g
      case decEq word g of
         (Yes Refl) => do ShowState
                          Won
                          ShowState
                          Exit
         (No contra) => case guesses of
                             0 => do ShowState
                                     Lost 
                                     ShowState
                                     Exit
                             (S k) => gameLoop


data HistoryVect : (invLength : Nat) -> (head : Word) -> (guessList : List Word) -> Type where
   NilHistory : HistoryVect 6 NilWord [NilWord]
   AddHistory : (newHead : Word) -> (oldHistory : HistoryVect (S n) oldHead oldList) -> HistoryVect n newHead (newHead :: oldList)

data Game : GameState -> Type where
   GameStart : Game NotRunning
   GameWon : (word : Word) -> Game NotRunning
   GameLost : (word : Word) -> Game NotRunning
   InProgress : (word : Word) -> (guesses : Nat) 
                  -> (history : HistoryVect guesses lastGuess guessList)
                  -> Game (Running guesses word lastGuess)


compareWords : (word : Vect n Char) -> (lastGuess : Vect n Char) -> (charList : Vect 5 Char) -> String
compareWords [] [] charList = ""
compareWords (x :: xs) (y :: ys) charList = case x == y of
                                                 False => case isElem y charList of
                                                               (Yes prf) => "~ " ++ compareWords xs ys charList
                                                               (No contra) => ". " ++ compareWords xs ys charList
                                                 True => "$ " ++ compareWords xs ys charList


showSymbols : (word : Word) -> (lastGuess : Word) -> String
showSymbols (OKWord xs) (OKWord ys) = compareWords xs ys xs 
showSymbols _ _ = ". . . . . "


showLetters : Word -> String
showLetters NilWord = "_ _ _ _ _ "
showLetters (OKWord xs) = padRight 1 ' ' $ unwords $ map String.singleton $ map toUpper $ vectToList xs 


showBoards : (word : Word) -> HistoryVect guesses lastGuess guessList-> String
showBoards word NilHistory = ""
showBoards word (AddHistory lastGuess oldHistory) = showBoards word oldHistory
                                                      ++ "\n" ++ showSymbols word lastGuess  ++ "         " 
                                                      ++ showLetters lastGuess




fillNil : (guesses : Nat) -> String
fillNil 0 = ""
fillNil (S k) = "\n_ _ _ _ _          _ _ _ _ _ " 
                  ++ fillNil k


Show (Game g) where
   show GameStart = "Starting"
   show (GameWon word) = "Congratulations, you won! The word was: " ++ show word
   show (GameLost word) = "Poopoo, you lost. The word was: " ++ show word
   show (InProgress word guesses guessList) = "\nWordle in Idris"
                                              ++ showBoards word guessList 
                                              ++ fillNil guesses
                                              ++ "\nLegend: \".\" = incorrect letter; \"~\" = incorrect placement; \"$\" = correct placement"


wordle : GameLoop () NotRunning (const NotRunning)
wordle = do NewGame testWord
            gameLoop



data GameResult  : (ty : Type) -> (ty -> GameState) -> Type where
   OK : (res : ty) -> Game (outState_fn res) -> GameResult ty outState_fn
   OutOfFuel : GameResult ty outState_fn

ok : (res : ty) -> Game (outstate_fn res) -> IO (GameResult ty outstate_fn)
ok res st = pure (OK res st)




listToWord : List Char -> IO (Maybe Word)
listToWord (x :: y :: z :: w :: v :: xs) = case xs of
                                                [] => pure $ Just $ OKWord $ fromList $ x :: y :: z :: w :: v :: []
                                                (s :: ys) => pure Nothing

listToWord _ = pure Nothing


runCmd : Fuel -> Game inState -> GameCmd ty inState outState_fn -> IO (GameResult ty outState_fn)
runCmd fuel state (NewGame word) = ok () (InProgress word _ NilHistory)
runCmd fuel (InProgress word _ history) Won = ok () (GameWon word)
runCmd fuel (InProgress word _ history) Lost = ok () (GameLost word)
runCmd fuel (InProgress word _ history) (Guess guess) = ok () (InProgress word _ (AddHistory guess history))
runCmd fuel state ShowState = do printLn state
                                 ok () state
runCmd fuel state (Message str) = do putStrLn str
                                     ok () state
runCmd (More fuel) state ReadGuess = do input <- getLine
                                        word <- listToWord (map toLower (unpack input))
                                        case word of 
                                           Nothing => do putStrLn "Not a valid input!"
                                                         runCmd fuel state ReadGuess
                                           Just okWord => ok okWord state
runCmd fuel state (Pure res) = ok res state
runCmd fuel state (cmd >>= next) = do OK cmdRes newSt <- runCmd fuel state cmd
                                                | OutOfFuel => pure OutOfFuel
                                      runCmd fuel newSt (next cmdRes)
runCmd Dry _ _ = pure OutOfFuel

run : Fuel -> Game inState -> GameLoop ty inState outState_fn -> IO (GameResult ty outState_fn)
run Dry _ _ = pure OutOfFuel
run (More fuel) st Exit = ok () st
run (More fuel) st (cmd >>= next)
   = do OK cmdRes newSt <- runCmd fuel st cmd
           | OutOfFuel => pure OutOfFuel
        run fuel newSt (next cmdRes)
run (More fuel) st (cmd >> next)
   = do OK () newSt <- runCmd fuel st cmd
           | OutOfFuel => pure OutOfFuel
        run fuel newSt next


partial
main : IO ()
main = do ignore $ run forever GameStart wordle







