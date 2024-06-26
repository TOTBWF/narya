open Util
open Tbwd
open Syntax
open Term

type definition = Axiom of [ `Parametric | `Nonparametric ] | Defined of (emp, potential) term

val find_opt : Constant.t -> ((emp, kinetic) term * definition) option
val locked : unit -> bool
val run_empty : (unit -> 'a) -> 'a
val add : Constant.t -> (emp, kinetic) term -> definition -> unit
val add_error : Constant.t -> Reporter.Code.t -> unit
val run_with : Constant.t -> (emp, kinetic) term -> definition -> (unit -> 'a) -> 'a
val run_with_definition : Constant.t -> definition -> (unit -> 'a) -> 'a
val run_locked : (unit -> 'a) -> 'a
