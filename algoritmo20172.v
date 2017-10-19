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
(** Importamos a biblioteca funind.Recdef para que as definições das funções fossem aceitas pelo sistema                                   *)
(**
    2. Utilize a formalização do algoritmo de ordenação por inserção desenvolvida em sala como parâmetro. *)

(**Adaptamos a função que verifica o número de ocorrências de um natural em uma lista de naturais para o nosso contexto. A alteração feita em relação à que foi utilizada em sala, foi a mudança das definições utilizadas, que antes eram as definições feitas pelo professor, para definições pré-implementadas no sistema. *)

Fixpoint num_oc (n:nat) (l:list nat) : nat :=
  match l with
    | nil => 0
    | cons h tl =>
      match eq_nat_dec n h with
        | left _ => S (num_oc n tl)
        | right _ => num_oc n tl
      end
  end.

(**Novamente, essa definição segue da lista de exercício sobre a estrutura de listas, modificado para ser utilizado no nosso contexto. *)

Definition equiv l l' := forall n, num_oc n l = num_oc n l'.

Inductive ordenada : (list nat) -> Prop :=
  | nil_ord : ordenada nil
  | one_ord : forall n:nat, ordenada (cons n nil)
  | mult_ord : forall (x y : nat) (l : list nat), ordenada (cons y l) -> le x y -> ordenada (cons x (cons y l)).

Lemma ordenada_sub: forall l n, ordenada (n::l) -> ordenada l.
Admitted.

(**Utilizamos uma tática similar a que foi apresentada em sala, dividindo o algoritmo em duas partes: A parte que o maior elemento da lista é borbulhado para o fim e a parte que realiza a repetição disso, de forma recursiva, na lista, enquanto existirem elementos não ordenados, realizando o que seria o loop mais externo em uma implementação em linguagem imperativa.*)

(**A função bubbleSort_once foi baseada em uma função escrita pelo professor em sala. Basicamente o que ela faz é pegar uma lista de inteiros passados, comparar os dois primeiros elementos dessa lista, garantir que o menor elemento estará na primeira posição dessa lista e, de forma recursiva, tratar do resto dessa lista, fazendo essa permutação para a cauda da lista, de forma recursiva. Com essa função, como mencionado anteriormente, garantimos que o maior elemento da lista passada como parâmetro inicialmente se encontrará no fim dessa ao final.*)

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

(**A função bubbleSort, como comentado anteriormente, é a função principal do algoritmo de ordenação. Notamos que o pattern matching é basicamente o que foi feito em sala para o Insertion Sort. *)

Function bubbleSort (l : list nat) : list nat :=
  match l with
    | nil => nil
    | cons n l' => bubbleSort_once (cons n (bubbleSort l'))
  end.

(**Utilizamos a notação vista no arquivo Lists.v do livro Software Foundations para facilitar a vizualização das computações abaixo. *)
Notation "a :: l" := (cons a l)(at level 60, right associativity).

(**Computações feitas em cima da nossa definição para mostrar que o algoritmo realmente funciona para as listas que colocamos.*)

Compute (bubbleSort (2 :: 1 :: nil)).
Compute (bubbleSort (2 :: 1 :: 0 :: nil)).
Compute (bubbleSort (3 :: 4 :: 2 :: 1 :: 5 :: nil)).

(**Alguns lemas auxiliares para a prova da corretude do algoritmo.*)
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

(**O teorema que prova a correção. Reaproveitamos esse teorema da formalização do algoritmo Insertion Sort, pois o que precisamos provar são as mesmas coisas, que: para qualquer lista l, a lista obtida l' é equivalente, ou seja, possui os mesmos elementos de l (porém, permutados) e que a lista l' é ordenada.*)

(**Lema auxiliar que mostra que a função auxiliar do algoritmo retorna uma lista ordenada(parcialmente), ou seja, ordena localmente.*)
Lemma bubbleSort_once_ordena: forall l a, ordenada l -> ordenada (bubbleSort_once (a :: l)).
  induction l.
  - intros a H.
    rewrite bubbleSort_once_equation.
    apply one_ord.
  - intros a' H.
    rewrite bubbleSort_once_equation.
    destruct (le_lt_dec a' a).
    + generalize dependent l. 
      intro l.
      case l.
      * intros IH H.
        rewrite bubbleSort_once_equation.
        apply mult_ord.
        apply one_ord.
        exact l0.
      * intros n l' IH H.
        rewrite bubbleSort_once_equation.
        destruct (le_lt_dec a n).
        ** apply mult_ord.
           assert (H': bubbleSort_once(a :: n :: l') = a :: bubbleSort_once (n :: l')).
           {
             rewrite bubbleSort_once_equation.
             destruct (le_lt_dec a n).
             - reflexivity.
             - apply le_not_lt in l1. 
               contradiction.
           }
           rewrite <- H'.
           apply IH.
           apply ordenada_sub in H.
           exact H.
           exact l0.
        ** apply mult_ord.
           assert (H': bubbleSort_once(a :: n :: l') = n :: bubbleSort_once (a :: l')).
           {
             rewrite bubbleSort_once_equation.
             destruct (le_lt_dec a n).
             - apply le_not_lt in l2.
               contradiction.
             - reflexivity.
           } 
           rewrite <- H'.
           apply IH.
           apply ordenada_sub in H.
           exact H.
           inversion H; subst.
           apply le_trans with a.
           exact l0.
           assert (H': ordenada (bubbleSort_once (a :: n :: l'))).
           {
             apply IH.
             exact H2.
           }
           exact H4.
    + generalize dependent l.
      intro l.
      case l.
      *intros IH H.
       rewrite bubbleSort_once_equation.
       apply mult_ord.
       ** apply one_ord.
       ** destruct (le_dec a a').
         *** exact l1.
         *** admit.
      *intros.
Qed.

(**Lema auxiliar que mostra a equivalência entre uma lista l e euma lista l', que é a lista retornada pela função auxiliar bubbleSort_once. *)
Lemma bubbleSort_once_equiv: forall l, equiv (bubbleSort_once l) l.
Proof.
  intro l.
  functional induction (bubbleSort_once l).
  -unfold equiv in *.
   intro n.
   remember (h1 :: tl) as l eqn: H.
   simpl num_oc.
   destruct (Nat.eq_dec n h0).
   +rewrite IHl0.
    trivial.
   +rewrite IHl0.
    trivial.
  -unfold equiv in *.
   intro n.
   simpl num_oc at 1.
   destruct(Nat.eq_dec n h1).
   +rewrite IHl0.
    simpl.
    destruct(Nat.eq_dec n h0).
    *destruct(Nat.eq_dec n h1).
     **reflexivity.
     **contradiction.
    *destruct(Nat.eq_dec n h1).
     **reflexivity.
     **contradiction.
    +rewrite IHl0.
     simpl.
     destruct(Nat.eq_dec n h0).
     *destruct(Nat.eq_dec n h1).
      **contradiction.
      **trivial.
     *destruct(Nat.eq_dec n h1).
      **contradiction.
      **trivial.
  -unfold equiv.
   intro.
   trivial. 
Qed.

(**Lema da correção do algoritmo principal, bubbleSort. *)

Theorem correcao: forall l, (equiv (bubbleSort l) l) /\ ordenada (bubbleSort l).
Proof.
  split.
  -generalize dependent l.
   induction l.
   +simpl bubbleSort.
    unfold equiv.
    reflexivity.
   +simpl bubbleSort.
    unfold equiv in *.
    intro n.
    unfold num_oc at 2.
    destruct(Nat.eq_dec n a).
    *rewrite <- IHl.
     assert(H: num_oc n (a :: bubbleSort l) = S (num_oc n (bubbleSort l))).
     **simpl num_oc at 1.
       destruct(Nat.eq_dec n a).
       ***reflexivity.
       ***contradiction.
     **rewrite <- H.
       generalize n.
       fold (equiv (bubbleSort_once (a :: bubbleSort l)) (a :: bubbleSort l)).
       apply bubbleSort_once_equiv.
    *rewrite <- IHl.
     assert(H: num_oc n (a :: bubbleSort l) = (num_oc n (bubbleSort l))).
     **simpl num_oc at 1.
       destruct (Nat.eq_dec n a).
       ***contradiction.
       ***reflexivity.
     **rewrite <- H.
       generalize n.
       fold (equiv (bubbleSort_once (a :: bubbleSort l)) (a :: bubbleSort l)).
       apply bubbleSort_once_equiv.
  -induction l.
   +simpl bubbleSort.
    apply nil_ord.
   +simpl bubbleSort.
    apply bubbleSort_once_ordena.
    exact IHl.
Qed.
    
Theorem correcao_comp: forall (l:list nat), {l' | equiv l l' /\ ordenada l'}.
Proof.
  intro l.
  exists (bubbleSort l).
  apply correcao.
Qed.
