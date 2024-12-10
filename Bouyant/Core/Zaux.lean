import LeanSearchClient

#leansearch r#"Theorem Zopp_le_cancel :
  forall x y : Z,
  (-y <= -x)%Z -> Z.le x y.
."#

#leansearch r#"y < x -> x ≠ y."#
#check Int.ne_of_lt

theorem Zopp_le_cancel
  (x y : Int)
  (h : -y ≤ -x)
  : x ≤ y :=
  by simp [Int.le_of_neg_le_neg h]

#leansearch r#"y < x -> x ≠ y."#

theorem Zgt_not_eq
  (x y : Int)
  (h : y < x)
  : x ≠ y :=
  by
    intro h'
    apply Int.lt_irrefl x
    rw [h']
    exact lt_of_lt_of_eq h h'
