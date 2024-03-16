Definition option_bind {A B: Type} (a: option A) (f: A -> option B): option B :=
  match a with
  | Some x => f x
  | None => None
  end.

Definition option_map_map {A B C: Type} (f: A -> B -> C) (a: option A) (b: option B): option C :=
  match a with
  | Some a' => option_map (f a') b
  | _ => None
  end.

Definition option_apply {A B : Type} (f: option (A -> B)) (a: A): option B :=
  match f with
  | Some f' => Some (f' a)
  | _ => None
  end.
