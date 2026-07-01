(* begin hide *)
Require Import Arith List Lia.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.
(* end hide*)

(**
Este trabalho apresenta uma prova formal da correção do algoritmo de ordenação por borbulhamento (a função [bs] a seguir). A formalização foi feita no assistente de provas Coq. O assistente de provas Coq utiliza o sistema de Dedução Natural, o que o torna adequado para o desenvolvimento de atividades computacionais no curso de Lógica Computacional 1. O Coq permite a extração de código certificado em diversas linguagens funcionais, como Ocaml, Haskell e Scheme. *)

(** Iniciaremos definindo a função [bubble] que recebe uma lista de naturais como argumento, e percorre esta lista comparando elementos consecutivos. Chamamos este processo de borbulhamento: *)

Function bubble (l: list nat ) {measure length l} :=
  match l with
  | nil => nil
  | x::nil => x::nil
  | x::y::l =>
      if x <=? y
      then x::(bubble (y::l))
            else y::(bubble (x::l))
            end.
Proof.
  - auto.
  - auto.
Defined.

(** Observe que esta função não é estruturalmente recursiva porque, xpor exemplo, a lista [(x::l)] não é uma sublista da lista original [(x::y::l)]. Neste caso, utilizamos [Function] para construir esta função e precisamos fornecer a medida que decresce em cada chamada recursiva, além de provar que esta medida efetivamente decresce a cada chamada recursiva. Por exemplo, [bubble (2::1::nil)] retorna a lista [(1::2::nil)].

 *)

Eval compute in bubble (2::1::nil).

(**

<<
   = 1 :: 2 :: nil
     : list nat
>>

*)

Eval compute in bubble (3::2::1::nil).

(**

<<
    = 2 :: 1 :: 3 :: nil
     : list nat
>>

*)

(** A função principal, ou seja, o algoritmo bubble sort propriamente dito, é dada pela função [bs] abaixo que recebe uma lista de naturais como argumento:

*)

Fixpoint bs (l: list nat) :=
  match l with
  | nil => nil
  | h::l' => bubble (h::(bs l'))
  end.           
(* begin hide *)
Eval compute in (bs (1::2::nil)).
Eval compute in (bs (2 :: 1::nil)).
Eval compute in (bs (3 :: 2 :: 1::nil)).
(* end hide *)

(** Sabemos que aplicar a função [bubble] a uma lista qualquer, não necessariamente vai retornar uma lista ordenada, mas o lema [bubble_sorted] a seguir nos mostra que se o primeiro elemento é o único elemento fora de ordem em uma lista, ao aplicarmos a função [bubble], obtemos uma lista ordenada: *)

Lemma bubble_sorted: forall l, Sorted le l -> bubble l = l.
Proof.
  intros l H.
  functional induction (bubble l).
  - (* Caso 1: A lista é vazia (nil) *)
    reflexivity.
  - (* Caso 2: A lista tem apenas um elemento (x :: nil) *)
    reflexivity.
  - (* Caso 3: A lista tem dois ou mais elementos (x :: y :: l) e x <= y *)
    inversion H as [| ? ? H_sorted H_hdrel]; subst.
    rewrite IHl0; auto.
  - (* Caso 4: A lista tem dois ou mais elementos (x :: y :: l) mas o teste x <= y falhou *)
    inversion H as [| ? ? H_sorted H_hdrel]; subst.
    inversion H_hdrel; subst.
    apply Nat.leb_gt in e0.
    lia.
Qed.  
Lemma bubble_min: forall l a y, y <= a -> Sorted le (y::l) -> HdRel le y (bubble (a::l)).
Proof.
  intros l a y Hya Hyl.
  destruct l.
  - rewrite bubble_equation. constructor. lia.
  - rewrite bubble_equation. destruct (a <=? n) eqn:E.
    + constructor. lia.
    + inversion Hyl; subst. inversion H2; subst. constructor. lia.
Qed.

Lemma bubble_insert_sorted: forall l, Sorted le l -> forall x, Sorted le (bubble (x::l)).
Proof.
  induction l.
  - intros H x. simpl. constructor.
    + constructor.
    + constructor.
  - intros H x. rewrite bubble_equation. destruct (x <=? a) eqn:E.
    + apply Nat.leb_le in E.
      rewrite bubble_sorted by assumption.
      constructor.
      * assumption.
      * constructor. lia.
    + apply Nat.leb_gt in E.
      constructor.
      * apply IHl. inversion H; subst; assumption.
      * apply bubble_min; auto. lia.
Qed.

Lemma bs_sorted: forall l, Sorted le (bs l).
Proof.
  induction l.
  - simpl. constructor.
  - simpl. apply bubble_insert_sorted. assumption.
Qed.

(** A seguir, mostraremos que o algoritmo bubblesort (função [bs]) gera como saída uma permutação da lista de entrada. O lema a seguir nos diz que a função [bubble] também gera uma permutação da entrada: *)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  intros l.
  functional induction (bubble l).
  - (* Caso 1: A lista é vazia (nil) *)
    reflexivity.
  - (* Caso 2: A lista tem apenas um elemento (x :: nil) *)
    reflexivity.
  - (* Caso 3: A lista tem dois ou mais elementos (x :: y :: l) e x <= y *)
    apply perm_skip. assumption.
  - (* Caso 4: A lista tem dois ou mais elementos (x :: y :: l) mas x > y *)
    apply perm_trans with (y :: x :: l0).
    + apply Permutation_sym. apply perm_swap.
    + apply perm_skip. assumption.
Qed.

(** O lema [bs_correto] a seguir, nos mostra que o algoritmo [bs] gera uma permutação da lista de entrada: *)

Lemma bs_permuta: forall l, Permutation l (bs l).
Proof.
  induction l.
  - (* Caso 1: A lista é vazia (nil) *)
    simpl. reflexivity.
  - (* Caso 2: A lista tem cabeça a e cauda l *)
    simpl. apply perm_trans with (a :: bs l).
    + apply perm_skip. assumption.
    + apply bubble_perm.
Qed.

(** Por fim, a correção do algoritmo [bs] é obtida pelo teorema a seguir que estabelece que o algoritmo [bs] retorna uma permutação da lista de entrada que está ordenada: *)
    
Theorem bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l).
Proof.
  intros l. split.
  - apply bs_sorted.
  - apply bs_permuta.
Qed.  

(** Repositório: %\url{https://github.com/flaviodemoura/bubble_sort}% *)
