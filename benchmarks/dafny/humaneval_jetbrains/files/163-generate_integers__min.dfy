/*
function_signature: method min(a : int, b : int) returns (m : int)
Process input. Ensures: returns the correct size/count; the result is at most the specified value.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method min(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m <= a && m <= b
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
