/- Constants -/
def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

/- Type checking -/
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check true

/- Evaluation / Computation -/
#eval 5 * 4
#eval m + 2
#eval b1 && b2

/- Function types -/
#check Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check (Nat → Nat) → Nat -- functional
#check Nat × Nat -> Nat
#check (5, 6)

/- Nat methods -/
#check Nat.succ
#check Nat.add_le_add_iff_left
#check Nat.succ 3
#eval Nat.add 4 5
#eval ((5, 6).1, (5, 6).2)

/- Types as objects -/
def α:Type := Nat
def β := Bool
def ρ := (Nat × Nat)
def cross:Type := α × β
def list_of_list:Type := List (List Nat)

/- Type universes -/
#check Type
#check Type 1
#check Type 2
#check Type 3
#check Type 4
def P (a:Type i) : Type i := Prod a a

/- Structures -/

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := {
  x := 0.0,
  y := 0.0
}

def p1 : Point := { x := 3.3, y := 23.23 }

def distance(x: Point)(y:Point) : Float :=
  (Float.pow (x.x - y.x) 2) + (Float.pow (x.y - y.y) 2)

def zeroX1 (p : Point) : Point :=
  { x := 0, y := p.y }

def zeroX2 (p : Point) : Point :=
  { p with x := 0 }

#eval distance origin p1

-- Inductive types

inductive Booly where
  | false : Booly
  | true : Booly
deriving Repr

inductive Naty where
  | zero : Naty
  | succ (n:Naty) : Naty
deriving Repr

def Naty.add (x:Naty) (y: Naty) : Naty :=
  match x with
    | zero => y
    | succ a => Naty.add a (succ y)

instance add : Add Naty where
  add := Naty.add

def isZero(n : Naty): Booly :=
  match n with
    | Naty.zero     => Booly.true
    | Naty.succ _ => Booly.false

#eval isZero (Naty.succ Naty.zero)

def Naty.toNat (x: Naty) : Nat :=
  match x with
    | Naty.zero => 0
    | Naty.succ x => 1 + (Naty.toNat x)

def Naty.fromNat (x: Nat) : Naty :=
  match x with
    | 0 => Naty.zero
    | Nat.succ n => (Naty.succ (Naty.fromNat n))

-- recursive functions

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

#eval even 17

-- polymorpism

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def floatOrigin : PPoint Float :=
  { x := 0.0, y := 0.0 }
def natOrigin : PPoint Nat :=
  { x := 0, y := 0 }

#eval floatOrigin
#eval natOrigin

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Int | Sign.neg => Float :=
  match s with
    | Sign.neg => 0.4
    | Sign.pos => 3

-- recursive and polymorphic, with implicit type

def length {α : Type} (xs: List α) : Nat :=
  match xs with
    | []      => 0
    | _ :: ys => 1 + (length ys)

def length1 (xs: List α) : Nat :=
  match xs with
    | []      => 0
    | _ :: ys => 1 + (length ys)

-- Option type

def head {α : Type} (xs : List α) : Option α :=
  match xs with
    | []      => none
    | y :: _ => some y

-- product type

def sevens : String × Int × Nat := ("VII", 7, 4 + 3)

-- type classes

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

instance : Plus Float where
  plus := Float.add

open Plus(plus)

#eval plus 4 5
#eval plus 4.3 5.2

def List.sumall {α} [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumall

def xx : List Nat := [1,2,3,4,5]
#eval xx.sumall

-- functors

class FunctorType (f : Type → Type) where
  map {α β : Type} : (α → β) → f α → f β

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

-- option type

def andThen (opt : Option α) (fn : α -> Option β) : Option β :=
  match opt with
    | none => none
    | some x => fn x
infixl:55 " &-> " => andThen

def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)

def firstThird (xs : List α) : Option (α × α) :=
  xs[0]? >>= fun first : α =>
    xs[2]? >>= fun third : α =>
      some (first, third)

-- error type monads

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

def andThenYikes (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x

-- monads

class MonadType (m : Type → Type) where
  pure {α : Type} : α → m α
  bind {α β : Type} : m α → (α → m α) → m α

-- algorithms

inductive BinTree (α : Type) where
  | node
    (left : Option (BinTree α))
    (right : Option (BinTree α))
    (key : Nat) (value : α)
deriving Repr

inductive TreeDirection where
  | left
  | right

def TreePath := List TreeDirection




-- instance : Monad
