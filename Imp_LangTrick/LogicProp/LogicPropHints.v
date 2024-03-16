From Imp_LangTrick Require Import LogicProp.

Create HintDb logic_props.

Global Hint Constructors LogicProp : logic_props.
Global Hint Constructors prop_rel : logic_props.
Global Hint Constructors prop_args_rel : logic_props.
Global Hint Constructors eval_prop_args_rel : logic_props.
Global Hint Constructors eval_prop_rel : logic_props.
Global Hint Constructors transformed_prop_exprs : logic_props.
Global Hint Constructors transformed_prop_exprs_args : logic_props.
