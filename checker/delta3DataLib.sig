signature delta3DataLib =
sig
  include Abbrev
  type dat = (string * string list list) list
  val read_dat   : string -> dat                 (* "@name count" sections of integer rows *)
  val section    : dat -> string -> string list list
  val num_tm     : string -> term
  val int_tm     : string -> term
  val row_tm     : string -> string list -> term (* spec: one char per column, n = num, i = int *)
  val rows_tm    : string -> string list list -> term
  val nums_tm    : string list -> term           (* a num list *)
  val intss_tm   : string list list -> term      (* an int list list *)
  val define     : string -> term -> thm         (* name = term *)
  val from_conv  : conv                          (* evaluates  from_<type> <literal>  to a cv literal *)
  val timed      : string -> string -> ('a -> 'b) -> 'a -> 'b   (* theory name, label; appends to timings.tsv *)
end
