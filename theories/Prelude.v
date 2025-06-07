From Stdlib Require Export Setoid Morphisms SetoidDec.

Generalizable Variables X.

Section option_eq.

  Context `{Setoid X}.
  
  Definition option_eq : relation (option X) :=
    option_rect _
    (fun x1 =>
      option_rect _
      (equiv x1)
      False
    )
    (
      option_rect _
      (fun _ => False)
      True
    ).

  Instance option_eq_Reflexive : Reflexive option_eq.
  Proof.
  Admitted.

  Instance option_eq_Symmetric : Symmetric option_eq.
  Proof.
  Admitted.

  Instance option_eq_Transitive : Transitive option_eq.
  Proof.
  Admitted.

  #[export] Program Instance option_eq_Equivalence : Equivalence option_eq.
  #[export] Program Instance option_eq_Setoid : Setoid (option X).

End option_eq.
