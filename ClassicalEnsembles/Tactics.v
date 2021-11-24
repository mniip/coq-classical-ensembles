Require Import Coq.Logic.FunctionalExtensionality.
Require Import Classical_Prop.

Require Import ClassicalEnsembles.Core.

Global Hint Extern 3
  => match goal with
     | p : ?P |- context G[@EnsembleLEM ?X ?P ?T ?F]
       => rewrite (@ensemble_lem_true X P T F p)
     | p : ~?P |- context G[@EnsembleLEM ?X ?P ?T ?F]
       => rewrite (@ensemble_lem_false X P T F p)
     end : sets.

Ltac unfold_comprehension :=
  multimatch goal with
  | |- context K[In ?X (fun (x : ?X) => @?F x) ?y]
    => let K1 := context K[In X F y] in
       let K2 := context K[F y] in
       change K1 with K2; cbn beta
  | H : context K[In ?X (fun (x : ?X) => @?F x) ?y] |- _
    => let K1 := context K[In X F y] in
       let K2 := context K[F y] in
       change K1 with K2 in H; cbn beta in H
  end.

Ltac unset :=
  repeat first [ progress unfold Included in *
               | progress autorewrite with sets in *
               | progress unfold_comprehension
               | unset_goal
               | unset_hyp ]
with unset_nohyp :=
  repeat first [ progress unfold Included in *
               | progress autorewrite with sets in *
               | progress unfold_comprehension
               | unset_goal ]
with unset_goal :=
  multimatch goal with
  | |- context K[forall (x : ?X), @?G x]
    => lazymatch type of G with
       | _ -> ?Y
         => let T := open_constr:(_ : X -> Y) in
            let Z := fresh in
            let P := constr:(fun (Z : X -> Y)
                               => ltac:(let KZ := context K[forall (x : X), Z x]
                                        in exact KZ)) in
            refine (@eq_rect (X -> Y) T P _ G ltac:(fun_unset));
            [ lazy beta ]
      end
  | |- context K[fun (x : ?X) => @?G x]
    => lazymatch type of G with
       | _ -> ?Y
         => let T := open_constr:(_ : X -> Y) in
            let Z := fresh in
            let P := constr:(fun (Z : X -> Y)
                               => ltac:(let KZ := context K[fun (x : X) => Z x]
                                        in exact KZ)) in
            refine (@eq_rect (X -> Y) T P _ G ltac:(fun_unset))
       end
  end
with unset_hyp :=
  multimatch goal with
  | H : context K[forall (x : ?X), @?G x] |- _
    => lazymatch type of G with
       | _ -> ?Y
         => let T := open_constr:(_ : X -> Y) in
            let Z := fresh in
            let P := constr:(fun (Z : X -> Y)
                               => ltac:(let KZ := context K[forall (x : X), Z x]
                                        in exact KZ)) in
            let H' := fresh in
            pose proof (@eq_rect (X -> Y) G P H T ltac:(fun_unset)) as H';
            lazy beta in H';
            clear H;
            rename H' into H
      end
  | H : context K[fun (x : ?X) => @?G x] |- _
    => lazymatch type of G with
       | _ -> ?Y
         => let T := open_constr:(_ : X -> Y) in
            let Z := fresh in
            let P := constr:(fun (Z : X -> Y)
                               => ltac:(let KZ := context K[fun (x : X) => Z x]
                                        in exact KZ)) in
            let H' := fresh in
            pose proof (@eq_rect (X -> Y) G P H T ltac:(fun_unset)) as H';
            lazy beta in H';
            clear H;
            rename H' into H
      end
  end
with fun_unset :=
  apply functional_extensionality;
  intros ?;
  progress unset_nohyp;
  reflexivity.

Ltac setext :=
  lazymatch goal with
  | |- context K[@eq (Ensemble ?X) ?A ?B]
    => rewrite <- (@ensemble_extensionality X A B)
  | H : context K[@eq (Ensemble ?X) ?A ?B] |- _
    => rewrite <- (@ensemble_extensionality X A B) in H
  end.

Ltac setsolve_intuition :=
  repeat first [ progress intuition (unshelve eauto with sets)
               | progress unset
               | setext ].

Ltac setsolve_firstorder :=
  repeat first [ progress intuition (unshelve eauto with sets)
               | progress unset
               | setext
               | progress firstorder with sets ].

Ltac setsolve :=
  setsolve_intuition;
  try (apply NNPP; setsolve_intuition; fail).
