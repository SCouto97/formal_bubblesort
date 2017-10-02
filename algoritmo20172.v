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

(**Precisamos terminar a prova. *)
Theorem correcao: forall l, (equiv l (bubbleSort l)) /\ ordenada (bubbleSort l).
Proof.
induction l.
- split.
  + unfold bubbleSort.
    unfold equiv.
    intros.
    trivial. 
  + apply nil_ord.
- destruct IHl. 
  split.
  + unfold equiv in *.
    intro x.
Admitted.

Theorem correcao_comp: forall (l:list nat), {l' | equiv l l' /\ ordenada l'}.
Proof.
  intro l.
  exists (bubbleSort l).
  apply correcao.
Qed.