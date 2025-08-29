

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: method min(a : int, b : int) returns (m : int)
Process input. Ensures: returns the correct size/count; the result is at most the specified value.
*/
// </vc-description>

// <vc-spec>
method min(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m <= a && m <= b
// </vc-spec>

// <vc-code>
{
  if a <= b {
    m := a;
  } else {
    m := b;
  }
}
// </vc-code>

method max(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m >= a && m >= b
{
  assume{:axiom} false;
}
method generate_integers(a : int, b : int) returns (result: seq<int>)
  // post-conditions-start
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] % 2 == 0
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] in [2, 4, 6, 8]
  // post-conditions-end
{
  assume{:axiom} false;
}