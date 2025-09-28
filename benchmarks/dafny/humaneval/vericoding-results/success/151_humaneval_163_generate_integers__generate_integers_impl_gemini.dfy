// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int {
  if a < b then a else b
}

function max(a: int, b: int): int {
  if a > b then a else b
}
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
  /* code modified by LLM (iteration 5): [switched to manual sequence construction to fix compilation errors] */
  var low := min(a, b);
  var high := max(a, b);
  result := [];
  if low <= 2 && 2 <= high { result := result + [2]; }
  if low <= 4 && 4 <= high { result := result + [4]; }
  if low <= 6 && 6 <= high { result := result + [6]; }
  if low <= 8 && 8 <= high { result := result + [8]; }
}
// </vc-code>
