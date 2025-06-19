From CoIndEx Require Export Prelude.

(** * Positive Conatural Numbers *)

Module Pos.

  CoInductive conat := cozero | cosucc : conat -> conat.

  (** ** Basic Definitions *)

  Definition pred (n : conat) : option conat :=
    match n with
    | cozero => None
    | cosucc n' => Some n'
    end.

  (** ** Setoid *)

  CoInductive conat_eq : conat -> conat -> Prop :=
    | cozero_conat_eq_cozero : conat_eq cozero cozero
    | cosucc_conat_eq_cosucc :
        forall n' m',
          conat_eq n' m' ->
          conat_eq (cosucc n') (cosucc m').

  Instance conat_eq_Reflexive : Reflexive conat_eq.
  Proof.
    cofix conat_eq_Reflexive.
    intros [].
    all: now constructor.
  Qed.

  Instance conat_eq_Symmetric : Symmetric conat_eq.
  Proof.
    cofix conat_eq_Symmetric.
    all: inversion 1.
    all: now constructor.
  Qed.
      
  Instance conat_eq_Transitive : Transitive conat_eq.
  Proof.
    cofix conat_eq_Transitive.
    do 2 inversion 1.
    all: constructor.
    all: etransitivity.
    all: eassumption.
  Qed.

  #[export] Program Instance conat_eq_Equivalence : Equivalence conat_eq.
  #[export] Program Instance conat_eq_Setoid : Setoid conat.

  #[export] Instance cosucc_Proper : Proper (equiv ==> equiv) cosucc.
  Proof.
    now constructor.
  Qed.

  #[export] Instance pred_Proper : Proper (equiv ==> equiv) pred.
  Proof.
    now inversion 1.
  Qed.

  (** ** Frobenius *)

  Definition frob (n : conat) : conat :=
    match n with
    | cozero => cozero
    | cosucc n' => cosucc n'
    end.

  Lemma eq_frob :
    forall n,
      n = frob n.
  Proof.
    now intros [].
  Qed.

End Pos.

(** * Negative Conatural Numbers *)

Module Neg.

  CoInductive conat :=
    {
      pred : option conat
    }.

  (** ** Basic Definitions *)

  Definition cozero : conat :=
    {|
      pred := None
    |}.

  Definition cosucc (n : conat) : conat :=
    {|
      pred := Some n
    |}.

  Arguments cosucc n /.

  (** ** Setoid *)

  CoInductive conat_eq : relation conat :=
    | pred_conat_eq_pred :
        forall n m n' m',
          n = {| pred := Some n' |} ->
          m = {| pred := Some m' |} ->
          conat_eq n' m' ->
          conat_eq n m
    | cozero_conat_eq_cozero :
          conat_eq cozero cozero.

  Ltac inject_pred :=
    repeat match goal with
           | [ H : {| pred := Some _ |} = {| pred := Some _ |} |- _ ] =>
               injection H; intro; subst; clear H
           end;
    subst.

  Instance conat_eq_Reflexive : Reflexive conat_eq.
  Proof.
    cofix conat_eq_Reflexive.
    intros [[]].
    all: now econstructor.
  Qed.

  Instance conat_eq_Symmetric : Symmetric conat_eq.
  Proof.
    cofix conat_eq_Symmetric.
    inversion 1; inject_pred.
    all: now econstructor.
  Qed.
      
  Instance conat_eq_Transitive : Transitive conat_eq.
  Proof with (try easy).
    cofix conat_eq_Transitive.
    do 2 (inversion 1; inject_pred)...
    econstructor...
    etransitivity.
    all: eassumption.
  Qed.

  #[export] Program Instance conat_eq_Equivalence : Equivalence conat_eq.
  #[export] Program Instance conat_eq_Setoid : Setoid conat.

  #[export] Instance pred_Proper : Proper (equiv ==> equiv) pred.
  Proof.
    now inversion 1; subst.
  Qed.

  #[export] Instance cosucc_Proper : Proper (equiv ==> equiv) cosucc.
  Proof.
    inversion 1; inject_pred.
    all: now econstructor.
  Qed.

  (** ** Frobenius *)

  Definition frob (n : conat) : conat :=
    match n with
    | {| pred := Some n' |} => {| pred := Some n' |}
    | {| pred := None    |} => {| pred := None    |}
    end.

  Lemma eq_frob :
    forall n,
      n = frob n.
  Proof.
    now intros [[]].
  Qed.

End Neg.

Module Pos_iso_Neg.

  Import Pos Neg.

  CoFixpoint Pos_from_Neg (n : Neg.conat) : Pos.conat :=
    match n with
    | {| pred := Some n' |} => Pos.cosucc (Pos_from_Neg n')
    | {| pred := None    |} => Pos.cozero
    end.

  Instance Pos_from_Neg_Proper : Proper (equiv ==> equiv) Pos_from_Neg.
  Proof.
    cofix Pos_from_Neg_Proper.
    intros n m H1.
    all: inversion H1 as [? ? ? ? H2 H3 H4 H5 H6|]; subst.
    -
      rewrite Pos.eq_frob with (n := Pos_from_Neg {| pred := Some n' |}).
      rewrite Pos.eq_frob with (n := Pos_from_Neg {| pred := Some m' |}).
      constructor.
      apply Pos_from_Neg_Proper.
      exact H4.
    -
      reflexivity.
  Qed.

  CoFixpoint Neg_from_Pos (n : Pos.conat) : Neg.conat :=
    match n with
    | Pos.cozero => Neg.cozero
    | Pos.cosucc n' => Neg.cosucc (Neg_from_Pos n')
    end.

  Fact Neg_from_Pos_cozero :
    Neg_from_Pos Pos.cozero = Neg.cozero.
  Proof.
    rewrite Neg.eq_frob with (n := Neg_from_Pos Pos.cozero).
    reflexivity.
  Qed.

  Fact Neg_from_Pos_cosucc :
    forall n,
    Neg_from_Pos (Pos.cosucc n) = Neg.cosucc (Neg_from_Pos n).
  Proof.
    intros n.
    rewrite Neg.eq_frob with (n := Neg_from_Pos (Pos.cosucc n)).
    reflexivity.
  Qed.

  Instance Neg_from_Pos_Proper : Proper (equiv ==> equiv) Neg_from_Pos.
  Proof.
    cofix Neg_from_Pos_Proper.
    intros n m H1.
    inversion H1 as [eq1 eq2|? ? H2 eq1 eq2]; subst.
    -
      reflexivity.
    -
      do 2 rewrite Neg_from_Pos_cosucc.
      econstructor; try reflexivity.
      apply Neg_from_Pos_Proper.
      exact H2.
  Qed.

  Proposition Pos_from_Neg_from_Pos :
    forall n,
      Pos_from_Neg (Neg_from_Pos n) == n.
  Proof.
    cofix Pos_from_Neg_from_Pos.
    intros [|n'].
    -
      rewrite Pos.eq_frob with (n := Pos_from_Neg (Neg_from_Pos Pos.cozero)).
      reflexivity.
    -
      rewrite Pos.eq_frob with (n := Pos_from_Neg (Neg_from_Pos (Pos.cosucc n'))).
      constructor.
      apply Pos_from_Neg_from_Pos.
  Qed.

  Proposition Neg_from_Pos_from_Neg :
    forall n,
      Neg_from_Pos (Pos_from_Neg n) == n.
  Proof.
    cofix Neg_from_Pos_from_Neg.
    intros [[n'|]].
    -
      rewrite Neg.eq_frob with (n := Neg_from_Pos (Pos_from_Neg {| pred := Some n' |})).
      econstructor; try reflexivity.
      apply Neg_from_Pos_from_Neg.
    -
      rewrite Neg.eq_frob with (n := Neg_from_Pos (Pos_from_Neg {| pred := None |})).
      reflexivity.
  Qed.

End Pos_iso_Neg.
