import Mathlib.Data.Matrix.Notation

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m>0) (hn : n>0)

abbrev rowListofMat := List.map List.ofFn (List.ofFn M)

lemma rowListLength_eq_numRow : (rowListofMat M).length = m := by simp

lemma rowListofMat_elt_length_eq_numCol : ∀ i, ((rowListofMat M).get i).length = n := by simp

lemma rowLengthEq : ∀ i j, (List.ofFn (M i)).length = (List.ofFn (M j)).length := by simp

abbrev colListofMat := List.map List.ofFn (List.ofFn M.transpose)

lemma colListLength_eq_numCol : (colListofMat M).length = n := by simp

abbrev list_allZero (l : List Rat) : Bool := l.all (fun x => (x==0))

lemma nonzInRowList_imp_nonzInColList (h : ∃ r ∈ rowListofMat M, ¬list_allZero r) :
  ∃ c ∈ colListofMat M, ¬list_allZero c := by
  rcases h with ⟨row,row_rl,hrow⟩
  rw [List.all_eq_true] at hrow; push_neg at hrow
  rcases hrow with ⟨x,xrow,xn0⟩
  have : List.indexOf x row < (colListofMat M).length := by
    rw [colListLength_eq_numCol]
    have := List.indexOf_lt_length.mpr row_rl
    rw [←rowListofMat_elt_length_eq_numCol M ⟨(rowListofMat M).indexOf row,this⟩]
