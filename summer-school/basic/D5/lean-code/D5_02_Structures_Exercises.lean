-- D5_02 exercises: easy Tree and Graph functions.
-- This file avoids harder tasks such as balanced trees, duplicate removal,
-- and graph proofs.

-- Frames: Tree definition / More Trees / Exercises.
inductive Tree (a : Type) where
  | nil : Tree a
  | node : Tree a -> a -> Tree a -> Tree a
  deriving Repr

def sampleTree : Tree Nat :=
  .node (.node .nil 1 .nil) 3 (.node .nil 5 .nil)

def exSize : Tree a -> Nat
  | .nil => by
      sorry
  | .node l _ r => by
      sorry

def exDepth : Tree a -> Nat
  | .nil => by
      sorry
  | .node l _ r => by
      sorry

def exReflect : Tree a -> Tree a
  | .nil => by
      sorry
  | .node l x r => by
      sorry

def exSearch [BEq a] (x : a) : Tree a -> Bool
  | .nil => by
      sorry
  | .node l y r => by
      sorry

-- Frames: Inductive Graph / Exercises: Graph Functions.
inductive Graph (a : Type) where
  | empty : Graph a
  | vertex : a -> Graph a
  | overlay : Graph a -> Graph a -> Graph a
  | connect : Graph a -> Graph a -> Graph a
  deriving Repr

def sampleGraph : Graph Nat :=
  .overlay (.vertex 1) (.connect (.vertex 1) (.vertex 2))

def exVertexCount : Graph a -> Nat
  | .empty => by
      sorry
  | .vertex _ => by
      sorry
  | .overlay g h => by
      sorry
  | .connect g h => by
      sorry

def exDirectEdges : Graph a -> List (a × a)
  | .empty => by
      sorry
  | .vertex _ => by
      sorry
  | .overlay g h => by
      sorry
  | .connect (.vertex a) (.vertex b) => by
      sorry
  | .connect g h => by
      sorry

