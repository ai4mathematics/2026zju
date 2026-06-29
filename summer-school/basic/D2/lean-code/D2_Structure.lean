/-
  D2_Structure.lean

  Live demo file for structures, field access, and structure update.
-/

namespace D2Structure

/-! ## A mathematical record type: integer vectors in the plane -/

structure Vector2 where
  x : Int
  y : Int
  deriving Repr, BEq, DecidableEq

def zeroVec : Vector2 :=
  { x := 0, y := 0 }

def u : Vector2 :=
  { x := 3, y := 4 }

#eval u
#eval u.x
#eval u.y

def Vector2.add (u v : Vector2) : Vector2 :=
  { x := u.x + v.x, y := u.y + v.y }

def Vector2.neg (u : Vector2) : Vector2 :=
  { x := -u.x, y := -u.y }

def Vector2.dot (u v : Vector2) : Int :=
  u.x * v.x + u.y * v.y

#eval Vector2.add u { x := -1, y := 2 }
#eval Vector2.neg u
#eval Vector2.dot u { x := 5, y := 6 }

theorem add_x (u v : Vector2) :
    (Vector2.add u v).x = u.x + v.x := by
  rfl

theorem add_y (u v : Vector2) :
    (Vector2.add u v).y = u.y + v.y := by
  rfl

theorem vector_eta (u : Vector2) :
    { x := u.x, y := u.y } = u := by
  cases u
  rfl

/-! ## Structures can bundle data and properties -/

structure PointOnDiagonal where
  x : Int
  y : Int
  onDiagonal : x = y
  deriving Repr, BEq, DecidableEq

def diag3 : PointOnDiagonal :=
  { x := 3, y := 3, onDiagonal := rfl }

#eval diag3.x
#eval diag3.y

theorem diagonal_coordinates_equal (p : PointOnDiagonal) : p.x = p.y :=
  p.onDiagonal

/-! ## A small environment-like structure for a later expression example -/

structure LinearEnv where
  xValue : Int
  yValue : Int
  deriving Repr, BEq, DecidableEq

def LinearEnv.lookup (env : LinearEnv) (name : String) : Option Int :=
  if name = "x" then
    some env.xValue
  else if name = "y" then
    some env.yValue
  else
    none

def env : LinearEnv :=
  { xValue := 10, yValue := 20 }

#eval env
#eval env.lookup "x"
#eval env.lookup "z"

/-!
Exercise ideas:
1. Define a structure for rational numbers with numerator and denominator.
2. Define addition or negation for a simple vector structure.
3. Define a structure bundling data with a property.
-/

end D2Structure
