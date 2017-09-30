(** 116297 - Tópicos Avançados em Computadores - 2017/2           **)
(** Provas Formais: Uma Introdução à Teoria de Tipos - Turma B    **)
(** Prof. Flávio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Aluno:                                                        **)
(** Matrícula:                                                    **)

(** Atividade: Formalizar um algoritmo ordenação de sua preferência. *)

(** Esta atividade pode ser realizada individualmente ou em dupla. *)

(** Algumas dicas:
    1. Utilize a biblioteca Arith do Coq. Com isto você terá diversas propriedades sobre os números naturais, e listas de números naturais para utilizar. *)

Require Import Arith.
Print list.

Function bubblesort_once l (measure length l) :=
 |cons h0 (cons h1 tl) =>
  match le_lt_dec



(**
    2. Utilize a formalização do algoritmo de ordenação por inserção desenvolvida em sala como parâmetro. *)
