(* based on examples from https://github.com/uwplse/pumpkin-pi/blob/master/plugin/src/options.ml *)

(** Create options that can be set in files using our plugin. *)

let checker_certify_opt = ref (true)


(** Set HoareChecker Certify  *)
let _ = Goptions.declare_bool_option {
    Goptions.optdepr = false; (* not deprecated *)
    Goptions.optkey = ["HoareChecker"; "Certify"];
    Goptions.optread = (fun () -> !checker_certify_opt);
    Goptions.optwrite = (fun b -> checker_certify_opt := b);
  }

let is_checker_certify () = !checker_certify_opt
    

(** Set HoareChecker Timeout n *)

let checker_timeout_opt = ref (None)

let _ = Goptions.declare_int_option {
    Goptions.optdepr = false;
    Goptions.optkey = ["HoareChecker"; "Timeout"];
    Goptions.optread = (fun () -> !checker_timeout_opt);
    Goptions.optwrite = (fun n -> checker_timeout_opt := n);
  }

let is_checker_timeout () =
  match !checker_timeout_opt with
  | Some n -> true
  | None -> false


let get_checker_timeout () = !checker_timeout_opt

