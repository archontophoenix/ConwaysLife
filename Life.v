Require Import Lists.List.
Require Import ZArith.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.

(* ************************************************************************** *)
(* Conway's Game of Life (https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life)
   is a well-studied cellular automaton that is the standard subject for
   Coderetreat (http://coderetreat.org/about). Coderetreat's goal is to
   promote test-driven development -- but as an alternative to writing tests, we
   ought to be able to prove an implementation of Conway's Game of Life to be
   correct.

   Here I have expressed the rules of Life in three different ways:

   1. As a boolean-valued function returnning whether the cell at location (x,y)
      at time t is alive, given the initial state (that is, the state at time
      zero), itself a boolean function of coordinates x and y.

   2. As a pair of mutually defined inductive types, Alive and Dead, that take
      an initial state function and coordinates (x,y,t).

   3. As a function from the (finite) set of live cells at one timestep to the
      set of live cells at the next timestep. (If you were implementing Life in
      order to display the results, you'd prefer this to function #1, because
      the latter has a runtime that is exponential in the timestep.)

   I would accept that the rules are proven correct if any two of the above
   formulations can be shown to be equivalent. *)
(* ************************************************************************** *)

(* ************************************************************************** *)
(* Generally useful definitions for the concept of "neighbor" *)

(* Enumeration of the coordinate deltas that count as neighboring cells *)
Definition neighborCoordDeltas :=
  ((-1,-1) :: (-1,0) :: (-1,1) :: (0,-1) :: (0,1) :: (1,-1) :: (1,0) :: (1,1)
     :: nil)%Z.

(* "count test l" tells how many elements of l pass test *)
Fixpoint count {A: Type} (test: A -> bool) (l: list A): nat :=
  fold_left (fun n a => if test a then S n else n) l 0.

(* ************************************************************************** *)
(* Conway's Life specified as a function **************************************)

(* alive init x y t
   tells whether, in a Conway's Life with initial state init,
   the cell at (x,y) at time t is alive *)
Fixpoint alive (init: Z -> Z -> bool) (x y: Z) (t: nat): bool :=
  let aliveAt (dxdy: Z * Z) (t: nat): bool :=
    match dxdy with
    | (dx,dy) => alive init (x + dx) (y + dy) t
    end
  in let liveNeighborCount (t: nat): nat :=
    count (fun dxdy => aliveAt dxdy t) neighborCoordDeltas
  in
    match t with
    | 0 =>
        init x y
    | S t' =>
       orb
         (andb (alive init x y t') (beq_nat (liveNeighborCount t') 2))
         (beq_nat (liveNeighborCount t') 3)
    end.

(* ************************************************************************** *)
(* Conway's Life specified as an inductive type *******************************)

(* LiveCount init x y t n examinedCoordDeltas remCoordDeltas
   means we've counted n live neighbors by looking at examinedCoordDeltas
   around (x,y) at time t, with remCoordDeltas left to examine *)
Inductive LiveCount (init: Z -> Z -> bool) (x y: Z):
        nat -> nat -> list (Z * Z) -> list (Z * Z) -> Prop :=
  | nextOneAlive (t n: nat) (dx dy: Z) (examined tail: list (Z * Z)):
      LiveCount init x y t n examined ((dx,dy) :: tail) ->
      Alive init (x + dx) (y + dy) t ->
      LiveCount init x y t (n + 1) ((dx,dy) :: examined) tail
  | nextOneDead (t n: nat) (dx dy: Z) (examined tail: list (Z * Z)):
      LiveCount init x y t n examined ((dx,dy) :: tail) ->
      Dead init (x + dx) (y + dy) t ->
      LiveCount init x y t n ((dx,dy) :: examined) tail

(* LiveNeighborCount init x y t n
   means that at time t, (x,y) has n live neighbors *)
with LiveNeighborCount (init: Z -> Z -> bool) (x y: Z): nat -> nat -> Prop :=
  | liveNeighborCount (t n: nat):
      LiveCount init x y t n neighborCoordDeltas nil ->
      LiveNeighborCount init x y t n

(* Alive init x y t
   means the cell at (x,y,t) is alive *)
with Alive (init: Z -> Z -> bool) (x y: Z): nat -> Prop :=
  | initAlive:
      init x y = true ->
      Alive init x y 0
  | survive2 (t: nat):
      Alive init x y t ->
      LiveNeighborCount init x y t 2 ->
      Alive init x y (S t)
  | surviveOrBorn3 (t: nat):
      LiveNeighborCount init x y t 3 ->
      Alive init x y (S t)

(* Dead init x y t
   means the cell at (x,y,t) is dead.
   You might be tempted to substitute
   "~ (Alive ...) for (Dead ...)",
   but that won't pass the strict positivity checker *)
with Dead (init: Z -> Z -> bool)  (x y: Z): nat -> Prop :=
  | initDead:
      init x y = false ->
      Dead init x y 0
  | staysDead (t n: nat):
      Dead init x y t ->
      LiveNeighborCount init x y t n ->
      n <> 3 ->
      Dead init x y (S t)
  | dies (t n: nat):
      Alive init x y t ->
      LiveNeighborCount init x y t n ->
      n <> 2 ->
      n <> 3 ->
      Dead init x y (S t)      
.

(* ************************************************************************** *)
(* Conway's Life specified as a function from a state (with finitely many live
   cells) at a given time step
   to the state at the following time step.
   Takes advantage of the fact that a cell in the next generation can be alive
   only if at or adjacent to a live cell in the previous generation. *********)

(* Coord: pairs of Zs as an ordered type *)
Module Coord := PairOrderedType Z_as_OT Z_as_OT.
(* CellSet: sets of (live) cell coordinates, implemented as an AVL tree *)
Module CellSet := FSetAVL.Make Coord.
(* Cells: a set of live cell coordinates *)
Definition Cells := CellSet.t.
(* The empty state *)
Definition EmptyCells: Cells := CellSet.empty.

Definition aliveInState (cells: Cells) (x y: Z): bool :=
  CellSet.mem (x,y) cells.

Definition liveNeighborCells (cells: Cells) (x y: Z): nat :=
  let
    aliveAt (dxdy: Z * Z): bool :=
      match dxdy with
      | (dx,dy) =>  aliveInState cells (x + dx) (y + dy)
      end
  in count aliveAt neighborCoordDeltas.

Definition aliveNextTick (cells: Cells) (x y: Z): bool :=
  orb
    (andb (aliveInState cells x y) (beq_nat (liveNeighborCells cells x y) 2))
    (beq_nat (liveNeighborCells cells x y) 3).

Definition addLiveSurrounding (prev: Cells) (xy: Z * Z) (next: Cells): Cells :=
  match xy with
  | (x,y) =>
    let addIfAlive (live: Cells) (dxdy: Z * Z): Cells :=
      match dxdy with
      | (dx,dy) =>
        if aliveNextTick prev (x + dx) (y + dy)
        then CellSet.add dxdy live
        else live
      end
    in fold_left addIfAlive neighborCoordDeltas next
  end.

Definition nextState (prev: Cells): Cells :=
  CellSet.fold (addLiveSurrounding prev) prev EmptyCells.

Fixpoint nthState (initState: Cells) (t: nat): Cells :=
  match t with
  | 0 => initState
  | S n => nextState (nthState initState n)
  end.

Definition aliveAtTime (initState: Cells) (x y: Z) (t: nat): bool :=
  aliveInState (nthState initState t) x y.

(* ************************************************************************** *)
(* How we'd like to show that these definitions of Life are equivalent *)
(* Equivalences involving states (Cells) can hold only for states with finitely
   many live cells, but the equivalance between the function and inductive type
   versions should hold even for states with infinitely many live cells *)

Definition lifeFunctionSameAsInductive: Prop :=
  forall init x y t,
    (alive init x y t = true <-> Alive init x y t)
      /\ (alive init x y t = false <-> Dead init x y t).

Definition lifeInductiveSameAsState: Prop :=
  forall initState x y t,
    (aliveAtTime initState x y t = true <->
         Alive (aliveInState initState) x y t)
      /\ (aliveAtTime initState x y t = false <->
         Dead (aliveInState initState) x y t).

Definition lifeStateSameAsFunction: Prop :=
  forall initState x y t,
    alive (aliveInState initState) x y t = aliveAtTime initState x y t.

