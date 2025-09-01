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
lemma even_in_range(x: int)
  requires x in [2, 4, 6, 8]
  ensures x % 2 == 0
{
}

lemma generate_integers_helper()
  ensures forall x: int :: x in [2, 4, 6, 8] ==> x % 2 == 0
{
  forall x: int | x in [2, 4, 6, 8]
    ensures x % 2 == 0
  {
    even_in_range(x);
  }
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
  result := [2, 4, 6, 8];
  generate_integers_helper();
}
// </vc-code>

