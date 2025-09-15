// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function IsMultipleOfTwo(x: int): bool { x % 2 == 0 }
predicate InDesiredRange(x: int) { x in [2,4,6,8] }
lemma EvenInRangeLemma(x: int)
  requires x in [2,4,6,8]
  ensures IsMultipleOfTwo(x) && InDesiredRange(x)
{
  // 2,4,6,8 are all even and in range
  
}
// </vc-helpers>

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)

  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] % 2 == 0
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] in [2, 4, 6, 8]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed invariant and added loop termination */
{
  var temp := [];
  var current := min(a, b);
  var max_val := if a > b then a else b;
  
  while current <= max_val
    invariant current <= max_val + 1
    invariant forall i :: 0 <= i && i < |temp| ==> IsMultipleOfTwo(temp[i]) && InDesiredRange(temp[i])
  {
    if IsMultipleOfTwo(current) && InDesiredRange(current) {
      temp := temp + [current];
    }
    current := current + 1;
  }
  result := temp;
}
// </vc-code>
