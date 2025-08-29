method min(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m <= a && m <= b
{
  assume{:axiom} false;
}
method max(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m >= a && m >= b
{
  assume{:axiom} false;
}

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: method generate_integers(a : int, b : int) returns (result: seq<int>)
Generate elements. Ensures: the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> a <= result[i] <= b || b <= result[i] <= a
  ensures if a <= b then result == seq(b - a + 1, i => a + i) else result == seq(a - b + 1, i => b + i)
// </vc-spec>
// <vc-code>
method generate_integers(a : int, b : int) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> a <= result[i] <= b || b <= result[i] <= a
  ensures if a <= b then result == seq(b - a + 1, i => a + i) else result == seq(a - b + 1, i => b + i)
{
  if a <= b {
    result := seq(b - a + 1, i => a + i);
  } else {
    result := seq(a - b + 1, i => b + i);
  }
}
// </vc-code>
