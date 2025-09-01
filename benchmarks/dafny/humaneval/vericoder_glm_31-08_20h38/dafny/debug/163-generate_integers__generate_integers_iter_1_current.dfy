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

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)
  // post-conditions-start
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] % 2 == 0
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] in [2, 4, 6, 8]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var L := if a <= b then a else b;
  var U := if a >= b then a else b;
  result := [];
  if L <= 2 <= U then
      result := result + [2];
  if L <= 4 <= U then
      result := result + [4];
  if L <= 6 <= U then
      result := result + [6];
  if L <= 8 <= U then
      result := result + [8];
}
// </vc-code>

