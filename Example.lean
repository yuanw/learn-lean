import Aesop

def cirno : String := "Cirno's Perfect Arithmetics Class has begun!"

example : α → α :=
  by aesop

#eval 1  + 2
#eval (1 + 2 : Nat)

structure Point where
  x : Float
  y : Float

def origin : Point := {x := 0.0, y := 0.0}

#eval origin.x



def List.last? {a : Type} (xs :List a) : Option a :=
  match xs with
  | [] => Option.none
  | y :: []=> Option.some y
  | _ :: ys=> last? ys
#eval ([] : List Int).last?
#eval ([1, 2, 3] : List Int).last?

def List.findFirst? {a : Type} (xs: List a) (pred : a -> Bool) : Option a :=
  match xs with
  | [] => Option.none
  | y :: ys => if pred y then some y else findFirst? ys pred

#eval ([1, 2, 3] : List Int).findFirst? (> 2)
