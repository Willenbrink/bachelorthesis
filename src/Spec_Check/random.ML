(*  Title:      Tools/Spec_Check/random.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

A Lehmer random number generator:
https://en.wikipedia.org/wiki/Lehmer_random_number_generator
We use int to avoid any float imprecision problems (and the seed is an int anyway)
a and m are selected according to the recommendation in the article above

Contains only those functions that rely on the internal integer representation of rand.
Should only be used by base_generator as that implements many helper functions.
*)

signature RANDOM =
sig
type rand
val new : unit -> rand
val next : rand -> rand

(* range (x,y) r in [x;y) *)
val range : int * int -> rand -> int * rand
(* perc r in [0;1). Theoretically 2^31 equidistant discrete steps *)
val perc : rand -> real * rand
val split : rand -> rand * rand

end

structure Random : RANDOM  =
struct

type rand = int

val a = 48271
val m = 2147483647 (* 2^31 - 1 *)

fun next seed = (seed * a) mod m

fun new () =
  Time.now ()
  |> Time.toMicroseconds
  |> (fn x => Int.max(1,x mod m)) (* The seed must be within [1;m) *)
  |> next (* Time is not sufficiently random when polled rapidly *)

fun range (min, max) r =
  if min > max then raise Domain
  else (min + ((max - min + 1) * r) div m, next r)

(* TODO test whether this works as well as it should *)
fun split r =
  let
    val r0 = next r
    val r1 = r - r0
  in
    (next r0, next r1)
  end

fun perc r = ((Real.fromInt r) / (Real.fromInt m), next r)

end
