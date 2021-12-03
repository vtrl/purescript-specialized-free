-- Derived from https://github.com/natefaubion/purescript-language-cst-parser
--
-- The MIT License (MIT)
--
-- Copyright (c) 2021 Nathan Faubion
--
-- Permission is hereby granted, free of charge, to any person obtaining a copy of
-- this software and associated documentation files (the "Software"), to deal in
-- the Software without restriction, including without limitation the rights to
-- use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
-- the Software, and to permit persons to whom the Software is furnished to do so,
-- subject to the following conditions:
--
-- The above copyright notice and this permission notice shall be included in all
-- copies or substantial portions of the Software.
--
-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
-- FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
-- COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
-- IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
-- CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
module Free.Teletype where

import Prelude

import Effect (Effect)
import Effect.Console (logShow)
import Data.List (List, (:), fromFoldable, reverse, uncons)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Unsafe.Coerce (unsafeCoerce)

-- QUEUE

-- | A common data type for values passed around in the free monad.
foreign import data UnsafeBoundValue ∷ Type

-- | A common data type for chaining monadic functions algebraically.
data BindsQueue c a b
  = Leaf (c a b)
  | Node (BindsQueue c a UnsafeBoundValue) (BindsQueue c UnsafeBoundValue b)

-- | Append a monadic function to the queue
qappend ∷ ∀ c a x b. BindsQueue c a x → BindsQueue c x b → BindsQueue c a b
qappend = unsafeCoerce Node

-- | Create a monadic function queue
qsingleton ∷ ∀ c a b. c a b → BindsQueue c a b
qsingleton = Leaf

-- | A data type for deconstructing a queue
data UnconsQueue c a b x
  = UnconsDone (c a b)
  | UnconsMore (c a x) (BindsQueue c x b)

-- | Deconstruct a queue into its view
unconsQueue ∷ ∀ c a b. BindsQueue c a b → UnconsQueue c a b UnsafeBoundValue
unconsQueue = uncons (unsafeCoerce UnconsDone) (unsafeCoerce UnconsMore)
  where
  uncons
    ∷ ∀ r
    . (c a b → r)
    → (∀ x. c a x → BindsQueue c x b → r)
    → BindsQueue c a b
    → r
  uncons done more = case _ of
    Leaf a → done a
    Node a b → uncons' more a b

  uncons'
    ∷ ∀ x r
    . (∀ z. c a z → BindsQueue c z b → r)
    → BindsQueue c a x
    → BindsQueue c x b
    → r
  uncons' cons l r = case l of
    Leaf k → cons (unsafeCoerce k) (unsafeCoerce r)
    Node l' r' → uncons' cons l' (Node (unsafeCoerce r') (unsafeCoerce r))

-- FREE MONAD

-- | A newtype wrapper over a monadic function for a Teletype
newtype TeletypeK a b = TeletypeK (a → Teletype b)

derive instance Newtype (TeletypeK a b) _

-- | A queue of monadic functions for a Teletype
type QTeletypeK = BindsQueue TeletypeK

-- | The teletype monad.
data Teletype a
  -- | Bread and butter.
  = Pure a
  | Bind (Teletype UnsafeBoundValue) (QTeletypeK UnsafeBoundValue a)
  -- | Custom instructions.
  | PutLine String
  | GetLine (String → a)

-- | Log some output.
putLine ∷ String → Teletype Unit
putLine = PutLine

-- | Get some input.
getLine ∷ Teletype String
getLine = GetLine identity

instance Functor Teletype where
  -- Existing `Bind`s only have operations appended to their queue of
  -- monadic functions, while non-`Bind`s are raised into binds first.
  --
  -- For example, if we map to a non-`Bind`:
  --
  -- > f <$> Pure 10
  --
  -- We'll then get:
  --
  -- > Bind (Pure 10) [\n -> Pure (f n)]
  --
  -- Likewise, if we map to a `Bind`:
  --
  -- > Bind (Pure 10) [\n -> Pure (f n), \n -> Pure (g n)]
  map f = case _ of
    Bind i q →
      Bind i (qappend q (qsingleton (TeletypeK (Pure <<< f))))
    i →
      Bind (unsafeCoerce i) (qsingleton (TeletypeK (Pure <<< (unsafeCoerce f))))

instance Apply Teletype where
  apply t1 t2 = do
    f ← t1
    x ← t2
    pure $ f x

instance Applicative Teletype where
  pure = Pure

instance Bind Teletype where
  -- Existing `Bind`s only have operations appended to their queue of
  -- monadic functions, while non-`Bind`s are raised into binds first.
  --
  -- For example, if we bind a non-`Bind`:
  --
  -- > Pure 10 >>= \n -> Pure (n + 10)
  --
  -- We'll then get:
  --
  -- > Bind (Pure 10) [\n -> Pure (n + 10)]
  --
  -- Likewise, if we bind a `Bind`:
  --
  -- > Bind (Pure 10) [\n -> Pure (n + 10), \n -> Pure (n + 10)]
  bind m f = case m of
    Bind i q →
      Bind i (qappend q (qsingleton (TeletypeK f)))
    i →
      Bind (unsafeCoerce i) (qsingleton (TeletypeK (unsafeCoerce f)))

instance Monad Teletype

-- INTERPRETER

type TeletypeState_ r =
  { i ∷ List String
  , o ∷ List String
  | r
  }

type TeletypeState = TeletypeState_ ()

type TeletypeResult a = TeletypeState_ (v ∷ a)

data TeletypeStack a
  = StackNil
  | StackBinds (TeletypeStack a) (QTeletypeK UnsafeBoundValue a)

data TeletypeStackUnwind a
  = UnwindStop a TeletypeState
  | UnwindBinds (TeletypeStack a) TeletypeState (QTeletypeK UnsafeBoundValue a)

runTeletype ∷ ∀ a. Teletype a → TeletypeState → TeletypeResult a
runTeletype = unsafeCoerce (flip $ go StackNil)
  where
  -- Interpret our teletype free monad in a stack-safe manner. Let's
  -- start "simple" by interpreting our custom instructions.
  go
    ∷ TeletypeStack UnsafeBoundValue
    → TeletypeState
    → Teletype UnsafeBoundValue
    → TeletypeResult UnsafeBoundValue
  go stack state = case _ of
    -- PutLine modifies our state by appending a line to the output,
    -- then it terminates computation by recursing into `Pure` with
    -- `unit` as the value. This mirrors the `String -> Teletype Unit`
    -- type we have for its smart constructor `putLine`.
    PutLine l →
      go stack (state { o = l : state.o }) (Pure (unsafeCoerce unit))
    -- GetLine modifies our state by uncons-ing a line from the input,
    -- it then passes this value onto the inner function that it's
    -- holding, which is `identity` for its smart constructor `getLine`.
    GetLine f →
      case uncons state.i of
        Just { head, tail } →
          go stack (state { i = tail }) (Pure (unsafeCoerce (f head)))
        Nothing →
          go stack state (Pure (unsafeCoerce (f "\n")))
    -- Bind does nothing to the state but it modifies the current stack.
    -- More specifically, it appends a `StackBinds` populated with its
    -- queue of monadic functions, before recursing into the inner
    -- monad.
    Bind i q →
      go (StackBinds stack q) state i
    -- Pure often represents the end of a monadic computation, and in
    -- this case, we start by unwinding the stack.
    --
    -- If there are no more items in the stack, then we can return our
    -- final result. Otherwise, we perform specific operations for
    -- whatever value we've popped.
    Pure a →
      case unwindStack a state stack of
        UnwindStop a' state' →
          { i: state'.i, o: reverse state'.o, v: a' }
        -- In this case, we're tasked with unwinding `StackBinds`. We're
        -- given the following variables to work with: the rest of the
        -- stack; the current state; and the queue of monadic functions.
        UnwindBinds stack_ state' queue →
          -- We start by dissecting our monadic function queue.
          case unconsQueue queue of
            -- If there are no more functions to apply, recurse using
            -- the rest of the stack, the current state, and the value
            -- of the last function applied to the `Pure` value.
            UnconsDone (TeletypeK k) →
              go stack_ state' (k a)
            -- If there are more functions to apply, push the popped
            -- `StackBinds` back to the stack except the queue is
            -- replaced by the tail of whatever was deconstructed.
            -- Use this new stack, the current state, adn the value
            -- of the freshly unconsed function applied to the `Pure`
            -- value.
            UnconsMore (TeletypeK k) queue' →
              go (StackBinds stack_ queue') state' (k a)

  unwindStack
    ∷ UnsafeBoundValue
    → TeletypeState
    → TeletypeStack UnsafeBoundValue
    → TeletypeStackUnwind UnsafeBoundValue
  unwindStack value state = case _ of
    StackNil →
      UnwindStop value state
    StackBinds stack_ queue →
      UnwindBinds stack_ state queue

main ∷ Effect Unit
main = do
  let
    i ∷ Teletype Int
    i = do
      a ← getLine
      b ← getLine
      putLine a
      putLine b
      pure 2

    r ∷ TeletypeResult Int
    r = runTeletype i
      { i: fromFoldable [ "hello", "world" ]
      , o: fromFoldable []
      }

  logShow r
