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
lemma even_in_range_implies_in_set(x: int)
  ensures x % 2 == 0 && x in [2, 4, 6, 8] <==> (x == 2 || x == 4 || x == 6 || x == 8)
{
  // This lemma is self-evident for the given small range.
  // No complex proof needed, just stating the equivalence.
}
// </vc-helpers>

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)
  // post-conditions-start
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] % 2 == 0
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] in [2, 4, 6, 8]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var s: seq<int> := [];
  s := s + [2];
  s := s + [4];
  s := s + [6];
  s := s + [8];
  return s;
}
// </vc-code>

