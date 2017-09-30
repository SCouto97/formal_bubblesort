(** 116297 - Tópicos Avançados em Computadores - 2017/2           **)
(** Provas Formais: Uma Introdução à Teoria de Tipos - Turma B    **)
(** Prof. Flávio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Alunos: Gabriel Nunes Ribeiro Silva
            Samuel Andrade do Couto                               **)
(** Matrículas: 150126689
                150021623                                         **)

(** Atividade: Formalizar um algoritmo ordenação de sua preferência. *)

(** Esta atividade pode ser realizada individualmente ou em dupla. *)

(** Algumas dicas:
    1. Utilize a biblioteca Arith do Coq. Com isto você terá diversas propriedades sobre os números naturais, e listas de números naturais para utilizar. *)

Require Import Arith.
Require Import Coq.funind.Recdef.
(**
    2. Utilize a formalização do algoritmo de ordenação por inserção desenvolvida em sala como parâmetro. *)

Fixpoint num_oc (n:nat) (l:list nat) : nat :=
  match l with
    | nil => 0
    | cons h tl =>
      match eq_nat_dec n h with
        | left _ => S (num_oc n tl)
        | right _ => num_oc n tl
      end
  end.

Definition equiv l l' := forall n, num_oc n l = num_oc n l'.

Inductive ordenada : (list nat) -> Prop :=
  | nil_ord : ordenada nil
  | one_ord : forall n:nat, ordenada (cons n nil)
  | mult_ord : forall (x y : nat) (l : list nat), ordenada (cons y l) -> le x y -> ordenada (cons x (cons y l)).

Function bubbleSort_once l {measure length l} :=
  match l with
    | cons h0 (cons h1 tl) =>
      match le_lt_dec h0 h1 with
        | left _ => cons h0 (bubbleSort_once (cons h1 tl))
        | right _ => cons h1 (bubbleSort_once (cons h0 tl))
      end
    | _ => l
  end.
Proof.
intros.
simpl.
auto.
intros.
simpl.
auto.
Defined.

Function BubbleSort (l : list nat) : list nat :=
  match l with
    | nil => nil
    | cons n l' => bubbleSort_once (cons n (BubbleSort l'))
  end.

Compute (BubbleSort (cons 2 (cons 1 nil))).
Compute (BubbleSort (cons 2 (cons 1 (cons 0 nil)))).
Compute (BubbleSort (cons 1 (cons 0 (cons 2 nil)))).


Lemma bubbleSort_once_nil: bubbleSort_once nil = nil.
Proof.
unfold bubbleSort_once.
simpl.
trivial.
Qed.

Lemma bubbleSort_once_one: forall x, bubbleSort_once (cons x nil) = cons x nil.
Proof.
intros.
unfold bubbleSort_once.
simpl.
trivial.
Qed.

Theorem correcao: forall l, (equiv l (bubbleSort_once l)) /\ ordenada (bubbleSort_once l).
Proof.
induction l.
- split.
  + unfold bubbleSort_once.
    simpl.
    unfold equiv.
    intros.
    trivial. 
  + apply nil_ord.
- destruct IHl. 
  + split.
  unfold equiv in *.
  intro x.
  +


Lemma bubbleSort_once_leq: forall a b l, a <= b -> bubbleSort_once(cons a(cons b l)) = cons a(bubbleSort (cons b l)).
Proof. 
intros a b l H1.
functional induction (bubbleSort_once (b::l)%list).
-rewrite IHl1.
-
-