-- D5_02: Extra inductive structures after the list block.
-- Frames: "Tree definition", "More Trees", and "Inductive Graph: Three Representations".

-- Frames: Tree definition / More Trees.
inductive Tree (a : Type) where
  | nil : Tree a
  | node : Tree a -> a -> Tree a -> Tree a
  deriving Repr

def size : Tree a -> Nat
  | .nil => 0
  | .node l _ r => size l + size r + 1

def depth : Tree a -> Nat
  | .nil => 0
  | .node l _ r => Nat.succ (Nat.max (depth l) (depth r))

def reflect : Tree a -> Tree a
  | .nil => .nil
  | .node l x r => .node (reflect r) x (reflect l)

def preorder : Tree a -> List a
  | .nil => []
  | .node l x r => x :: (preorder l ++ preorder r)

def inorder : Tree a -> List a
  | .nil => []
  | .node l x r => inorder l ++ (x :: inorder r)

def postorder : Tree a -> List a
  | .nil => []
  | .node l x r => postorder l ++ postorder r ++ [x]

def search [BEq a] (x : a) : Tree a -> Bool
  | .nil => false
  | .node l y r => x == y || search x l || search x r

def sampleTree : Tree Nat :=
  .node (.node .nil 1 .nil) 3 (.node .nil 5 .nil)

#eval size sampleTree
#eval depth sampleTree
#eval inorder sampleTree
#eval search 5 sampleTree

-- Frame: Inductive Graph: Three Representations.
inductive Graph (a : Type) where
  | empty : Graph a
  | vertex : a -> Graph a
  | overlay : Graph a -> Graph a -> Graph a
  | connect : Graph a -> Graph a -> Graph a
  deriving Repr

def vertexCount : Graph a -> Nat
  | .empty => 0
  | .vertex _ => 1
  | .overlay g h => vertexCount g + vertexCount h
  | .connect g h => vertexCount g + vertexCount h

def toEdgeList [BEq a] : Graph a -> List (a × a)
  | .empty => []
  | .vertex _ => []
  | .overlay g h => toEdgeList g ++ toEdgeList h
  | .connect (.vertex a) (.vertex b) => [(a, b)]
  | .connect g h => toEdgeList g ++ toEdgeList h

def sampleGraph : Graph Nat :=
  .overlay (.vertex 1) (.connect (.vertex 1) (.vertex 2))

#eval vertexCount sampleGraph
#eval toEdgeList sampleGraph

-- Exercises:
-- Frames: Exercises / Exercises: Graph Functions.
-- 1. Add a BST-style insert for Tree Nat.
-- 2. Write a more careful vertex-counting function that removes duplicates.
-- 3. Define hasEdge for Graph Nat.
