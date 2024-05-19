import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.Linarith

variable (M : Matrix (Fin m) (Fin n) Rat)

abbrev rowListofMat := List.map List.ofFn (List.ofFn M)

lemma rowListLength_eq_numRow : (rowListofMat M).length = m := by simp

lemma rowListofMat_elt_length_eq_numCol : ∀ i, ((rowListofMat M).get i).length = n := by simp

lemma rowLengthEq : ∀ i j, (List.ofFn (M i)).length = (List.ofFn (M j)).length := by simp

abbrev colListofMat := List.map List.ofFn (List.ofFn M.transpose)

lemma colListLength_eq_numCol : (colListofMat M).length = n := by simp

/-Row-reduced form
1. The first nonzero entry of every row must be 1
2. Each column containing the first nonzero entry of a row must have all its other
   entries as 0
-/

def row_allZerosBeforeFirstOne (row : List Rat) : Bool :=
  List.isPrefixOf (List.replicate (row.indexOf 1) 0) row

abbrev list_allZero (l : List Rat) : Bool := l.all (fun x => (x==0))

def isRowReduced_row (ri : List Rat) : Bool×(Option Nat) :=
  if list_allZero ri then (true,none)
  else
    if ri.indexOf 1 = ri.length then (false,none)
    else
      if row_allZerosBeforeFirstOne ri then (true,ri.indexOf 1)
      else (false,none)

def isRowReduced_col (cj : List Rat) : Bool := List.all (List.erase cj 1) (fun x => x==0)

--In a matrix that is in row-reduced form, the index of 1 in a row that isn't all zero is less than the length of the row
lemma indFirstOne_lt_rowLength (rl : List Rat) (h : (isRowReduced_row rl).1 = true) (h' : ¬(list_allZero rl)) :
  (((isRowReduced_row rl).2).getD 0) < rl.length := by
  unfold isRowReduced_row
  split_ifs with h1 h2
  · have : (isRowReduced_row rl).1 == false := by unfold isRowReduced_row; rw [if_pos h1, if_neg h']; rfl
    simp at h this; rw [h] at this; contradiction
  · show rl.indexOf 1 < rl.length
    apply List.indexOf_lt_length.mpr
    rcases lt_or_gt_of_ne h1 with indlt|indgt
    exact List.indexOf_lt_length.mp indlt
    have l1 := rl.indexOf_le_length (a:=1)
    have nl1 := not_le_of_gt indgt
    contradiction
  · have : (isRowReduced_row rl).1 == false := by
      unfold isRowReduced_row; rw [if_neg h', if_neg h2, if_neg h1]; rfl
    simp at h this; rw [h] at this; contradiction

def row_allZero (row : List Rat) : Bool := row.all (fun x => (x==0))

def isRowReducedAux (rl : List (List Rat)) (cl : List (List Rat)) (h : ∀ i, (rl.get i).length = cl.length) : Bool :=
  match rl with
  | [] => true
  | a::as =>
    have h0 : ∀ i, as.get i ∈ as := by intro i; rw [as.mem_iff_get]; use i
    have h0' : ∀ i, (as.get i).length = ((a::as).get i.castSucc).length := by
      intro i
      obtain ⟨n,hn⟩ := ((a::as).mem_iff_get).mp ((List.subset_cons a as) (h0 i))
      have l1 := h (Fin.castSucc i); have l2 := h n; rw [←l1, hn] at l2; exact l2
    if h1 : row_allZero a then isRowReducedAux as cl (by intro i; have := h (i.castSucc); rw [← (h0' i)] at this; exact this)
    else
      if h2 : (isRowReduced_row a).1 then
       (isRowReduced_col (cl.get ⟨(((isRowReduced_row a).2).getD 0),((h ⟨0,Nat.zero_lt_succ as.length⟩) ▸ indFirstOne_lt_rowLength a h2 h1)⟩)) ∨
          isRowReducedAux as cl (by intro i; have := h (i.castSucc); rw [← (h0' i)] at this; exact this)
      else false

--Checks whether matrix is in row-reduced form
def isRowReduced : Bool :=
  isRowReducedAux (rowListofMat M) (colListofMat M) (by rw [colListLength_eq_numCol]; exact (rowListofMat_elt_length_eq_numCol M))

/-
Row-reduced echelon form
1. The matrix must be row-reduced
2. All rows that have only 0s must occur before those that have a nonzero entry
3. If rows 1,...,r are the nonzero rows and the first nonzero entry for each of
these rows occurs in columns k₁,k₂,...,k_r, then  k₁< k₂<...< k_r
-/

--Gives list containing k₁,k₂,...,k_r
def nonzColIndices : List (List Rat) → List ℕ
  | [] => []
  | a::as =>
      if ¬(isRowReduced_row a).1 then []
      else [((isRowReduced_row a).2).getD 0] ++ (nonzColIndices as)

def isZeroMatrix : Bool := (rowListofMat M).all (fun x => (x.all (fun y => y==0 )))

def zeroRowsLast : Bool :=
  let rl := rowListofMat M
  let indOfLastNonzeroRow := rl.length-1-((rl.reverse).findIdx (fun x => (x.any (fun y => ¬(y==0)))))
  let indsOfZeroRows := (List.unzip (rl.indexesValues (fun x => x.all (fun x => x==0)))).1
  ([indOfLastNonzeroRow]++indsOfZeroRows).Sorted (·≤·)

def isRowReducedEchelon : Bool :=
  (isZeroMatrix M) ∨
    (isRowReduced M) ∧
      (zeroRowsLast M) ∧
        (nonzColIndices (List.filter (fun x => x.any (fun x => ¬x==0)) (rowListofMat M))).Sorted (·<·)

#eval isRowReducedEchelon !![(1:Rat)/2,0,-3,1,0;2,1,0,0,0]
#eval isRowReducedEchelon !![0,0;0,0]
#eval isRowReducedEchelon !![1,2,3;4,5,6;7,8,9]
#eval isRowReducedEchelon !![1,0;0,1]

def C := !![-1,0,1;2,1,0;0,0,(0:Rat)]
#eval isRowReducedEchelon C

#eval isRowReducedEchelon !![0,5,1;1,0,0;0,0,0]
#eval isRowReducedEchelon !![7,0,1;1,1,0;0,0,0;0,0,0]
#eval isRowReducedEchelon !![1,0,-3,0,1,2,0,0,0]
