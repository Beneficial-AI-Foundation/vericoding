

// <vc-helpers>
lemma EvenInRange(x: int)
  requires x in [2, 4, 6, 8]
  ensures x % 2 == 0
{
}
// </vc-helpers>

// <vc-spec>
method min(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m <= a && m <= b
// </vc-spec>
// <vc-code>
{
  result := [2, 4, 6, 8];
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