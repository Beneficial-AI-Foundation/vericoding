// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> result[i] in {2, 4, 6, 8}
  ensures forall i :: 0 <= i < |result| - 1 ==> result[i] < result[i + 1]
  ensures forall x :: x in result ==> (x >= a && x <= b) || (x >= b && x <= a)
  ensures forall x :: x in {2, 4, 6, 8} && ((x >= a && x <= b) || (x >= b && x <= a)) ==> x in result
// </vc-spec>
// <vc-code>
{
  var minVal := if a <= b then a else b;
  var maxVal := if a <= b then b else a;
  var res: seq<int> := [];
  if minVal <= 2 && 2 <= maxVal { res := res + [2]; }
  if minVal <= 4 && 4 <= maxVal { res := res + [4]; }
  if minVal <= 6 && 6 <= maxVal { res := res + [6]; }
  if minVal <= 8 && 8 <= maxVal { res := res + [8]; }
  result := res;
}
// </vc-code>
