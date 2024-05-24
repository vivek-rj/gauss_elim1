import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.Linarith

variable (M : Matrix (Fin m) (Fin n) Rat)

#check Vector.ofFn M

abbrev rowVecofMat := Vector.map Vector.ofFn (Vector.ofFn M)

#check rowVecofMat M

-- lemma rowListLength_eq_numRow : (rowListofMat M).length = m := by simp

-- lemma rowListofMat_elt_length_eq_numCol : ∀ i, ((rowListofMat M).get i).length = n := by simp

-- lemma rowLengthEq : ∀ i j, (List.ofFn (M i)).length = (List.ofFn (M j)).length := by simp

-- lemma rowListElt_eq : ∀ i, (rowListofMat M).get i = List.ofFn (M (i.cast (rowListLength_eq_numRow M))) := by
--   intro i; simp; rfl

abbrev colVecofMat := Vector.map Vector.ofFn (Vector.ofFn M.transpose)

-- lemma colListLength_eq_numCol : (colListofMat M).length = n := by simp

-- lemma colListElt_eq : ∀ i, (colListofMat M).get i = List.ofFn (M · (i.cast (colListLength_eq_numCol M))) := by
--   intro i; simp; rfl

/-Row-reduced form
1. The first nonzero entry of every row must be 1
2. Each column containing the first nonzero entry of a row must have all its other
   entries as 0
-/

#check Vector.replicate
#check Vector
#check List.isPrefixOf
#check List.take
#check List.indexOf
#check List.findIdx

-- def vector_isPrefixOf : Vector Rat k → Vector Rat k → Bool
-- | ⟨[],_⟩ , _ => true
-- | _ , ⟨[],_⟩ => false
-- | ⟨a::as,ha⟩ , ⟨b::bs,hb⟩ => a==b && vector_isPrefixOf ⟨as,congrArg Nat.pred ha⟩ ⟨bs,congrArg Nat.pred hb⟩

def vector_isPrefixOf : Vector Rat k → Vector Rat k → Bool :=
  fun v => fun w => List.isPrefixOf v.toList w.toList

-- def vector_findIdx (p : α → Bool)(v : Vector α k) : ℕ := go v.toList 0 where
--   @[specialize] go : List α → Nat → Nat
--   | [], n => n
--   | a :: l, n => bif p a then n else go l (n + 1)

def row_allZerosBeforeFirstOne (row : Vector Rat m) : Bool :=
  List.isPrefixOf (List.replicate (row.toList.indexOf 1) 0) row.toList

abbrev vec_allZero (v : Vector Rat k) : Bool := v.toList.all (fun x => (x==0))

def isRowReduced_row (ri : Vector Rat n) : Bool×(Option Nat) :=
  if vec_allZero ri then (true,none)
  else
    if ri.toList.indexOf 1 = ri.length then (false,none)
    else
      if row_allZerosBeforeFirstOne ri then (true,ri.toList.indexOf 1)
      else (false,none)

def isRowReduced_col (cj : Vector Rat m) : Bool := List.all (List.erase cj.toList 1) (fun x => x==0)

#check Vector.toList_length

--In a matrix that is in row-reduced form, the index of 1 in a row that isn't all zero is less than the length of the row
lemma indFirstOne_lt_rowLength (rl : Vector Rat k) (h : (isRowReduced_row rl).1 = true) (h' : ¬(vec_allZero rl)) :
  (((isRowReduced_row rl).2).getD 0) < rl.length := by
  unfold isRowReduced_row
  split_ifs with h1 h2
  · have : (isRowReduced_row rl).1 == false := by unfold isRowReduced_row; rw [if_pos h1, if_neg h']; rfl
    simp at h this; rw [h] at this; contradiction
  · show rl.toList.indexOf 1 < rl.length
    simp_rw [← rl.toList_length]
    apply List.indexOf_lt_length.mpr
    rcases lt_or_gt_of_ne h1 with indlt|indgt
    simp_rw [← rl.toList_length] at indlt
    exact List.indexOf_lt_length.mp indlt
    have l1 := rl.toList.indexOf_le_length (a:=1)
    have nl1 := not_le_of_gt indgt
    simp_rw [← rl.toList_length] at nl1
    contradiction
  · have : (isRowReduced_row rl).1 == false := by
      unfold isRowReduced_row; rw [if_neg h', if_neg h2, if_neg h1]; rfl
    simp at h this; rw [h] at this; contradiction

#check Vector.map

def testcl := Vector.map Vector.ofFn (Vector.ofFn !![1,4,7;2,5,8;3,6,9])

#check Vector.map (Vector.drop 1) testcl

def isRowReducedAux (rl : Vector (Vector Rat k2) k1) (cl : Vector (Vector Rat k1) k2) : Bool :=
  match rl with
  | ⟨[],_⟩ => true
  | ⟨a::as,ha⟩ =>
    if h1 : vec_allZero a then isRowReducedAux ⟨as,congrArg Nat.pred ha⟩ (Vector.map (Vector.drop 1) cl) --cl (by intro i; have := h (i.castSucc); rw [← (h0' i)] at this; exact this)
    else
      ∃ h2 : (isRowReduced_row a).1,
      (isRowReduced_col (cl.get ⟨(((isRowReduced_row a).2).getD 0),indFirstOne_lt_rowLength a h2 h1⟩)) ∨
          isRowReducedAux ⟨as,congrArg Nat.pred ha⟩ (Vector.map (Vector.drop 1) cl)

--Checks whether matrix is in row-reduced form
def isRowReduced : Bool :=
  isRowReducedAux (rowVecofMat M) (colVecofMat M)

/-
Row-reduced echelon form
1. The matrix must be row-reduced
2. All rows that have only 0s must occur before those that have a nonzero entry
3. If rows 1,...,r are the nonzero rows and the first nonzero entry for each of
these rows occurs in columns k₁,k₂,...,k_r, then  k₁< k₂<...< k_r
-/

--Gives list containing k₁,k₂,...,k_r
def nonzColIndices : List (Vector Rat k) → List ℕ
  | [] => []
  | a::as =>
      if ¬(isRowReduced_row a).1 then []
      else [((isRowReduced_row a).2).getD 0] ++ (nonzColIndices as)

-- def nonzColIndices : Vector (Vector Rat k1) k2 → List ℕ
--   | ⟨[],_⟩ => []
--   | ⟨a::as,ha⟩ =>
--       if ¬(isRowReduced_row a).1 then []
--       else [((isRowReduced_row a).2).getD 0] ++ (nonzColIndices ⟨as,congrArg Nat.pred ha⟩)

def isZeroMatrix : Bool := (rowVecofMat M).toList.all (fun x => (x.toList.all (fun y => y==0 )))

def zeroRowsLast : Bool :=
  let rl := (rowVecofMat M).toList
  let indOfLastNonzeroRow := rl.length-1-((rl.reverse).findIdx (fun x => (x.toList.any (fun y => ¬(y==0)))))
  let indsOfZeroRows := (List.unzip (rl.indexesValues (fun x => x.toList.all (fun x => x==0)))).1
  ([indOfLastNonzeroRow]++indsOfZeroRows).Sorted (·≤·)

def isRowReducedEchelon : Bool :=
  (isZeroMatrix M) ∨
    (isRowReduced M) ∧
      (zeroRowsLast M) ∧
        (nonzColIndices (List.filter (fun x => x.toList.any (fun x => ¬x==0)) (rowVecofMat M).toList)).Sorted (·<·)

#eval isRowReducedEchelon !![(1:Rat)/2,0,-3,1,0;2,1,0,0,0]
#eval isRowReducedEchelon !![0,0;0,0]
#eval isRowReducedEchelon !![1,2,3;4,5,6;7,8,9]
#eval isRowReducedEchelon !![1,0;0,1]

def C := !![-1,0,1;2,1,0;0,0,(0:Rat)]
#eval isRowReducedEchelon C

#eval isRowReducedEchelon !![0,5,1;1,0,0;0,0,0]
#eval isRowReducedEchelon !![7,0,1;1,1,0;0,0,0;0,0,0]
#eval isRowReducedEchelon !![1,0,-3,0,1,2,0,0,0]
