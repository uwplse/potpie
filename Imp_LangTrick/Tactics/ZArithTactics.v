From Coq Require Import ZArith Psatz.

Local Open Scope Z_scope.

Ltac inj_nat_to_z_helper tac :=
      do 40  (try tac Nat2Z.inj_add;
              try tac Nat2Z.inj_mul;
              (* try tac Nat2Z.inj_sub; *)
              try tac Nat2Z.inj_pow).

    Tactic Notation "inj_nat_to_z" := inj_nat_to_z_helper ltac:(fun H => rewrite H).

Tactic Notation "inj_nat_to_z" "in" hyp(H) := inj_nat_to_z_helper ltac:(fun lem => rewrite lem in H).


Ltac bring_out_front H front a b c d :=
            match type of H with
            | context P [?e * front] =>
                replace (e * front) with (front * e) in H by lia
            | _ => idtac 
            end;
            repeat ((rewrite Z.mul_shuffle3 with (n := a) (m := front) in H)
                    || (rewrite Z.mul_shuffle3 with (n := b) (m := front) in H)
                    || (rewrite Z.mul_shuffle3 with (n := c) (m := front) in H)
                    || (rewrite Z.mul_shuffle3 with (n := d) (m := front) in H)).

Ltac remember_of_nat :=
               repeat match goal with
                      | [ |- context P [Z.of_nat ?a] ] =>
                          let a' := fresh "z" in
                          remember (Z.of_nat a) as a'
                      | [ H: _ = Z.of_nat _ |- _ ] =>
                          idtac
                      | [ H: context P [Z.of_nat ?b] |- _ ] =>
                          let b' := fresh "z" in
                          remember (Z.of_nat b) as b'
                      end.

             Ltac Z_ify H :=
               match type of H with
               | (?a <= ?b)%nat =>
                   let Hz := fresh "Hz" in
                   assert (Hz : (Z.of_nat a) <= (Z.of_nat b)); [ inj_nat_to_z; try lia | ];
                   inj_nat_to_z in Hz
               | (?a < ?b)%nat =>
                   let Hz := fresh "Hz" in
                   assert (Hz : (Z.of_nat a) < (Z.of_nat b)); [ inj_nat_to_z; try lia | ];
                   inj_nat_to_z in Hz
               end.
