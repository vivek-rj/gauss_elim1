import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith
import GaussElim.ReducedEchelon1

-- variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m>0) (hn : n>0)

-- abbrev rowListofMat := List.map List.ofFn (List.ofFn M)

-- lemma rowListLength_eq_numRow : (rowListofMat M).length = m := by simp

-- lemma rowListofMat_elt_length_eq_numCol : ∀ i, ((rowListofMat M).get i).length = n := by simp

-- lemma rowLengthEq : ∀ i j, (List.ofFn (M i)).length = (List.ofFn (M j)).length := by simp

-- abbrev colListofMat := List.map List.ofFn (List.ofFn M.transpose)

-- lemma colListLength_eq_numCol : (colListofMat M).length = n := by simp

-- /-Row-reduced form
-- 1. The first nonzero entry of every row must be 1
-- 2. Each column containing the first nonzero entry of a row must have all its other
--    entries as 0
-- -/

-- def row_allZerosBeforeFirstOne (row : List Rat) : Bool :=
--   List.isPrefixOf (List.replicate (row.indexOf 1) 0) row

-- abbrev list_allZero (l : List Rat) : Bool := l.all (fun x => (x==0))

-- def isRowReduced_row (ri : List Rat) : Bool×(Option Nat) :=
--   if list_allZero ri then (true,none)
--   else
--     if ri.indexOf 1 = ri.length then (false,none)
--     else
--       if row_allZerosBeforeFirstOne ri then (true,ri.indexOf 1)
--       else (false,none)

-- def isRowReduced_col (cj : List Rat) : Bool := List.all (List.erase cj 1) (fun x => x==0)

-- --In a matrix that is in row-reduced form, the index of 1 in a row that isn't all zero is less than the length of the row
-- lemma indFirstOne_lt_rowLength (rl : List Rat) (h : (isRowReduced_row rl).1 = true) (h' : ¬(list_allZero rl)) :
--   (((isRowReduced_row rl).2).getD 0) < rl.length := by
--   unfold isRowReduced_row
--   split_ifs with h1 h2
--   · have : (isRowReduced_row rl).1 == false := by unfold isRowReduced_row; rw [if_pos h1, if_neg h']; rfl
--     simp at h this; rw [h] at this; contradiction
--   · show rl.indexOf 1 < rl.length
--     apply List.indexOf_lt_length.mpr
--     rcases lt_or_gt_of_ne h1 with indlt|indgt
--     exact List.indexOf_lt_length.mp indlt
--     have l1 := rl.indexOf_le_length (a:=1)
--     have nl1 := not_le_of_gt indgt
--     contradiction
--   · have : (isRowReduced_row rl).1 == false := by
--       unfold isRowReduced_row; rw [if_neg h', if_neg h2, if_neg h1]; rfl
--     simp at h this; rw [h] at this; contradiction

-- def row_allZero (row : List Rat) : Bool := row.all (fun x => (x==0))

-- def isRowReducedAux (rl : List (List Rat)) (cl : List (List Rat)) (h : ∀ i, (rl.get i).length = cl.length) : Bool :=
--   match rl with
--   | [] => true
--   | a::as =>
--     have h0 : ∀ i, as.get i ∈ as := by intro i; rw [as.mem_iff_get]; use i
--     have h0' : ∀ i, (as.get i).length = ((a::as).get i.castSucc).length := by
--       intro i
--       obtain ⟨n,hn⟩ := ((a::as).mem_iff_get).mp ((List.subset_cons a as) (h0 i))
--       have l1 := h (Fin.castSucc i); have l2 := h n; rw [←l1, hn] at l2; exact l2
--     if h1 : row_allZero a then isRowReducedAux as cl (by intro i; have := h (i.castSucc); rw [← (h0' i)] at this; exact this)
--     else
--       if h2 : (isRowReduced_row a).1 then
--        (isRowReduced_col (cl.get ⟨(((isRowReduced_row a).2).getD 0),((h ⟨0,Nat.zero_lt_succ as.length⟩) ▸ indFirstOne_lt_rowLength a h2 h1)⟩)) ∨
--           isRowReducedAux as cl (by intro i; have := h (i.castSucc); rw [← (h0' i)] at this; exact this)
--       else false

-- --Checks whether matrix is in row-reduced form
-- def isRowReduced : Bool :=
--   isRowReducedAux (rowListofMat M) (colListofMat M) (by rw [colListLength_eq_numCol]; exact (rowListofMat_elt_length_eq_numCol M))

-- /-
-- Row-reduced echelon form
-- 1. The matrix must be row-reduced
-- 2. All rows that have only 0s must occur before those that have a nonzero entry
-- 3. If rows 1,...,r are the nonzero rows and the first nonzero entry for each of
-- these rows occurs in columns k₁,k₂,...,k_r, then  k₁< k₂<...< k_r
-- -/

-- --Gives list containing k₁,k₂,...,k_r
-- def nonzColIndices : List (List Rat) → List ℕ
--   | [] => []
--   | a::as =>
--       if ¬(isRowReduced_row a).1 then []
--       else [((isRowReduced_row a).2).getD 0] ++ (nonzColIndices as)

-- def isZeroMatrix : Bool := (rowListofMat M).all (fun x => (x.all (fun y => y==0 )))

-- def zeroRowsLast : Bool :=
--   let rl := rowListofMat M
--   let indOfLastNonzeroRow := rl.length-1-((rl.reverse).findIdx (fun x => (x.any (fun y => ¬(y==0)))))
--   let indsOfZeroRows := (List.unzip (rl.indexesValues (fun x => x.all (fun x => x==0)))).1
--   ([indOfLastNonzeroRow]++indsOfZeroRows).Sorted (·≤·)

-- def isRowReducedEchelon : Bool :=
--   (isZeroMatrix M) ∨
--     (isRowReduced M) ∧
--       (zeroRowsLast M) ∧
--         (nonzColIndices (List.filter (fun x => x.any (fun x => ¬x==0)) (rowListofMat M))).Sorted (·<·)

--------------------------------------------------------------------------------------------------------------------

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m > 0) (hn : n > 0)

def I : Matrix (Fin m) (Fin m) Rat := Matrix.diagonal (fun _ => (1:Rat))

def eltScalarMul (c : Rat) (i : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i i (c-1)

def eltRowSwap (i : Fin m) (j : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    let newr := (I i)
    Matrix.updateRow (Matrix.updateRow I i (I j)) j newr

def eltRowAdd (i : Fin m) (j : Fin m) (c : Rat) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i j c

example (x : Rat) (l : List Rat) (k : l.indexOf x < l.length) : x ∈ l := by
  exact List.indexOf_lt_length.mp k

lemma findIdx_exists_of_lt_length (p : α → Bool) (l : List α) (h : l.findIdx p < l.length) : ∃ x∈l, p x
   := by
   have := List.findIdx_get (p:=p) (w:=h)
   use l.get ⟨List.findIdx p l, h⟩
   constructor
   · exact List.get_mem l (List.findIdx p l) h
   · exact this

lemma findIdx_notExists_of_eq_length (l : List α) (p : α → Bool) (hl : l.findIdx p = l.length) : ∀ x∈l, p x = false := by
  intro x xl
  by_cases h:p x
  have := List.findIdx_lt_length_of_exists ⟨x,xl,h⟩
  have := ne_of_lt this
  contradiction
  simpa using h

lemma findIdx_eq_length_of_notExists (l : List α) (p : α → Bool) (hl : ∀ x∈l, p x = false) : l.findIdx p = l.length := by
  -- contrapose hl
  -- push_neg at *
  -- rcases lt_or_gt_of_ne hl with lt|gt
  -- simp; exact findIdx_exists_of_lt_length (fun x ↦ p x) l lt
  induction' l with a as ih
  · simp
  · simp at hl; have ih' := ih hl.2
    rw [List.findIdx_cons, hl.1, cond_false]; simpa

lemma findIdx_le_length (l : List α) (p : α → Bool) : l.findIdx p ≤ l.length := by
  by_cases h : (∃ x∈l, p x)
  exact le_of_lt (List.findIdx_lt_length_of_exists h)
  push_neg at h; simp at h
  exact le_of_eq (findIdx_eq_length_of_notExists l p h)

def findNonzCol : ℕ := (colListofMat M).findIdx (fun col => ¬ list_allZero col)

lemma findNonzCol_le_numCol : (findNonzCol M) ≤ (colListofMat M).length := by
  unfold findNonzCol
  apply findIdx_le_length (colListofMat M) (fun col => ¬list_allZero col)

lemma nonzListHasNonz (h : ¬list_allZero l) : ∃ x∈l, x≠0 := by
  rw [List.all_eq_true] at h
  push_neg at h
  convert h; simp

lemma findNonzCol_get_HasNonz (h : findNonzCol M < (colListofMat M).length) :
  ∃ x ∈ (colListofMat M).get ⟨findNonzCol M,h⟩, x≠0 := by
  unfold findNonzCol at h
  have := List.findIdx_get (w:=h)
  simp only [Bool.not_eq_true, Bool.decide_eq_false] at this
  rw [Bool.not_iff_not] at this
  obtain ⟨x,hx,xn0⟩ := nonzListHasNonz this
  use x
  constructor
  unfold findNonzCol
  convert hx using 4; ext col
  simp_rw [←Bool.not_iff_not (b:=list_allZero col)]
  simp
  assumption

def isZeroMatrix' : Bool := findNonzCol M = (colListofMat M).length

-- lemma nonzInRowList_imp_nonzInColList : (∃ r ∈ rowListofMat M, ¬list_allZero r) ↔
--   ∃ c ∈ colListofMat M, ¬list_allZero c := by
--   sorry
  -- constructor
  -- intro h
  -- rcases h with ⟨row,row_rl,hrow⟩
  -- rw [List.all_eq_true] at hrow; push_neg at hrow
  -- rcases hrow with ⟨x,xrow,xn0⟩
  -- have : List.indexOf x row < (colListofMat M).length := by
  --   rw [colListLength_eq_numCol]
  --   have := List.indexOf_lt_length.mpr row_rl
  --   rw [←rowListofMat_elt_length_eq_numCol M ⟨(rowListofMat M).indexOf row,by convert this⟩]
  -- let col := (colListofMat M).get ⟨row.indexOf x,_⟩

-- lemma isZeroMatrix_eq : isZeroMatrix M = isZeroMatrix' M := by
--   by_cases h : isZeroMatrix' M
--   · unfold isZeroMatrix; rw [h,List.all_eq_true]
--     unfold isZeroMatrix' at h; simp only [decide_eq_true_eq] at h
--     contrapose h; push_neg at *
--     have := (nonzInRowList_imp_nonzInColList M).mp h
--     unfold findNonzCol
--     apply ne_of_lt
--     apply List.findIdx_lt_length_of_exists
--     convert this; simp
--   · simp at h; unfold isZeroMatrix; rw [h]; unfold isZeroMatrix' at h
--     unfold findNonzCol at h
--     simp only [decide_eq_false_iff_not] at h
--     sorry
    -- contrapose h; push_neg at *; simp; unfold findNonzCol
    -- simp_rw [←colListLength_eq_numCol M]
    -- apply findIdx_eq_length_of_notExists
    -- have : ∀ col ∈ (colListofMat M), list_allZero col := by
      -- intro col hcol
      -- simp
      -- intro x xcol
    --   let i := Fin.mk (col.indexOf x) (List.indexOf_lt_length.mpr xcol)
    --   let j := Fin.mk ((colListofMat M).indexOf col) (by convert List.indexOf_lt_length.mpr hcol)
    --   have hi : col.length = m := colListofMat_elt_length_eq_numRow' M col hcol
    --   let i' := Fin.cast (hi) i
    --   let j' := Fin.cast (colListLength_eq_numCol M) j
    --   have zero_elt := h i' j'
    --   have : M i' j' = x := by
    --     unfold_let i' i j' j
    --     simp only [Fin.cast_mk]
    --     rw [rowList_get M ⟨List.indexOf x col,List.indexOf_lt_length.mpr xcol⟩]

  -- · unfold isZeroMatrix; rw [h,List.all_eq_true]
  --   intro x xrl
  --   unfold isZeroMatrix' at h; simp only [decide_eq_true_eq] at h
  --   have h := findIdx_notExists_of_eq_length _ _ h; simp at h


-- Returns value of pivot and its location
def findPivot : (Option Rat)×(Fin m)×(Fin n) :=
  if h1 : findNonzCol M = (colListofMat M).length then (none,⟨0,hm⟩,⟨0,hn⟩)
  else
    if h2 : findNonzCol M < (colListofMat M).length then
      let pcol := (colListofMat M).get ⟨findNonzCol M,h2⟩
      have h3 : pcol.findIdx (fun x => x≠0) < pcol.length := by
        have h4 := findNonzCol_get_HasNonz M h2
        unfold_let pcol
        apply List.findIdx_lt_length_of_exists
        convert h4; simp
      have h2' : findNonzCol M < n := by simp_rw [←colListLength_eq_numCol M]; assumption
      have h3a : pcol.length = m := by unfold_let pcol; simp
      have h3' : List.findIdx (fun x => decide (x ≠ 0)) pcol < m := by
        rw [← h3a]; exact h3
      (pcol.get ⟨pcol.findIdx (fun x => x≠0),h3⟩,⟨pcol.findIdx (fun x => x≠0),h3'⟩,⟨findNonzCol M,h2'⟩)
    else
      have h4 := findNonzCol_le_numCol M
      have nh4 := not_le.mpr (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1))
      absurd h4 nh4

def pivotRowSwap : Matrix (Fin m) (Fin m) Rat :=
  if (findPivot M hm hn).1 = none then 1
  else eltRowSwap ⟨0,hm⟩ ((findPivot M hm hn).2).1

#eval pivotRowSwap !![0,0,0;0,1,0;0,0,1] (by linarith) (by linarith)
#check Option.ne_none_iff_isSome

def pivotImprove : Matrix (Fin m) (Fin m) Rat :=
  if h : (findPivot M hm hn).1 = none then 1
  else eltScalarMul (1/(((findPivot M hm hn).1).get (Option.ne_none_iff_isSome.mp h))) ⟨0,hm⟩

#eval pivotImprove !![0,0,0;0,2,0;0,0,1] (by linarith) (by linarith)

def pivotColElimBelow : List (Matrix (Fin m) (Fin m) Rat) :=
  if (findPivot M hm hn).1 = none then [1]
  else List.ofFn fun i : Fin (m-1) => eltRowAdd ⟨i+1,Nat.add_lt_of_lt_sub i.2⟩ ⟨0,hm⟩ (- M ⟨i+1,Nat.add_lt_of_lt_sub i.2⟩ ((findPivot M hm hn).2).2)

#eval pivotColElimBelow !![1,0,0;0,1,0;0,0,1] (by linarith) (by linarith)
#eval pivotColElimBelow !![0,1,3;0,-1,6;0,2,9] (by linarith) (by linarith)

def exmat := !![4,-5,3,2;1,-1,-2,-6;4,-4,-14,(18:Rat)]
def piv := findPivot exmat (by linarith) (by linarith)
#eval piv
def e1 := pivotRowSwap exmat (by linarith) (by linarith)
#eval e1
def e2 := pivotImprove exmat (by linarith) (by linarith)
#eval e2
#eval e2 * e1 * exmat
def elist := pivotColElimBelow (e2 * e1 * exmat) (by linarith) (by linarith)
#eval elist
#eval (List.prod (elist.reverse++[e2,e1]))*exmat
