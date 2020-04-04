Require Export mathcomp.ssreflect.all_ssreflect.
Require Export String List.
Require Import Psatz.
Require Import List.

Notation "x ∉ L" := (~ In x L) (at level 80).
Infix "∈" := In (at level 80).

Variable ident: Set.
Axiom ident_compare:  forall (m n: ident), { m = n } + { m <> n }.
Axiom ident_fresh: forall (L: seq.seq ident), { x & x ∉ L}.

Inductive type: Type :=
| tyBase : type
| tyArrow (T1 T2: type): type.

(* Later change string to an atom? *)
Inductive term: Type:=
| fVar (_: ident) : term
| bVar (_: nat) : term
| tLam (T: type) (t: term): term
| tApp (t1 t2: term): term
| tConst (_: ident): term
.

Definition ctx := list (ident * type).

(* A few notations *)
Infix "→" := tyArrow (at level 40).
Notation "# x" := (fVar x) (at level 0).
Notation "^ n" := (bVar n) (at level 0).

Fixpoint open' (t: term) (x: ident) (k: nat) :=
  match t with
  | ^n => if eqn n k then #x else ^n
  | tLam T t' => tLam T (open' t' x k.+1)
  | tApp t1 t2 => tApp (open' t1 x k) (open' t2 x k)
  | _ => t
  end.
Definition open t x := open' t x 0.

Fixpoint close' (t: term) (T: type) (x: ident) (k: nat) :=
  match t with
  | #y => if ident_compare x y then ^k else t
  | tLam T' t' => tLam T' (close' t' T x k)
  | tApp t1 t2 => tApp (close' t1 T x k) (close' t2 T x k)
  | _ => t
  end.
Definition close t T x := close' t T x 0.

Inductive lc : term -> Prop :=
| lc_Var : forall x, lc #x
| lc_Const: forall x, lc (tConst x)
| lc_App : forall t1 t2, lc t1 -> lc t2 -> lc (tApp t1 t2)
(* | lc_abs : forall T t, (exists L, forall x, x ∉ L -> lc (open t x)) -> lc (tLam T t) *)
| lc_abs : forall T t L, (forall x, x ∉ L -> lc (open t x)) -> lc (tLam T t)
.
Hint Constructors lc.

Fixpoint lc_at (t: term) (k: nat): bool :=
  match t with
  | ^n => n < k
  | tApp t1 t2 => lc_at t1 k && lc_at t2 k
  | tLam T t' => lc_at t' (S k)
  | _ => true
  end.

(*
Reserved Notation "Γ ⊢ t : T" (at level 70, t at next level).
Inductive has_type (Γ: ctx) : term -> type -> Type :=
| T_Var: forall x T, (x, T) ∈ Γ -> Γ ⊢ (tVar x) : T
| T_Abs: forall x t T1 T2,
    (x, T1) :: Γ ⊢ t : T2 ->
    Γ ⊢ (tLam x T1 t) : T1 → T2
| T_App: forall t1 t2 T11 T12,
    Γ ⊢ t1 : T11 → T12 ->
    Γ ⊢ t2 : T11 ->
    Γ ⊢ tApp t1 t2 : T12
| T_Const: forall k, Γ ⊢ k : tyBase
where "Γ ⊢ t : T" := (has_type Γ t T).

Reserved Notation "[ x ↦ s ] t" (at level 40).
Fixpoint subst (x: string) (s: term) (t: term): term :=
  match t with
  | tVar y => if eqb x y then s else t
  (* | tLam  *)
  | _ => t
  end
where "[ x ↦ s ] t" := (subst x s t).

Reserved Notation "Γ ⊢ s ≡ t : T" (at level 70, s, t at next level).
Inductive equiv (Γ: ctx): term -> term -> type -> Type :=
| Q_Refl: forall t T,
    Γ ⊢ t : T ->
    Γ ⊢ t ≡ t : T
| Q_Symm: forall t s T,
    Γ ⊢ t ≡ s : T ->
    Γ ⊢ s ≡ t : T
| Q_Abs: forall x s2 t2 T1 T2,
    (x, T1) :: Γ ⊢ s2 ≡ t2 : T2 ->
    Γ ⊢ tLam x T1 s2 ≡ tLam x T1 t2 : T1 → T2
| Q_App: forall s1 s2 t1 t2 T1 T2,
    Γ ⊢ s1 ≡ t1 : T1 → T2 ->
    Γ ⊢ s2 ≡ t2 : T1 ->
    Γ ⊢ tApp s1 s2 ≡ tApp t1 t2 : T2
where "Γ ⊢ s ≡ t : T" := (equiv Γ s t T).
 *)
