// <vc-preamble>
function nonzero_helper(arr: seq<real>): nat 
    decreases |arr|
{
    if |arr| == 0 then
        0
    else
        var rest_count := nonzero_helper(arr[1..]);
        if arr[0] == 0.0 then
            rest_count
        else
            rest_count + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Adding lemma to prove nonzero_helper upper bound */
lemma NonzeroBound(arr: seq<real>)
  ensures nonzero_helper(arr) <= |arr|
  decreases |arr|
{
  if |arr| == 0 {
  } else {
    NonzeroBound(arr[1..]);
    // By induction, nonzero_helper(arr[1..]) <= |arr|-1
    // Then nonzero_helper(arr) <= nonzero_helper(arr[1..]) + 1 <= (|arr|-1) + 1 = |arr|
  }
}
// </vc-helpers>

// <vc-spec>
method nonzero(arr: array<real>) returns (result: int)
    ensures 
        result <= arr.Length &&
        result == nonzero_helper(arr[..]) &&
        (arr.Length > 0 && arr[0] == 0.0 ==> 
            nonzero_helper(arr[1..]) == if result > 0 then result - 1 else 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Calling lemma to discharge bounds and assigning result */
{
  result := nonzero_helper(arr[..]);
  NonzeroBound(arr[..]);
  // The third ensures should hold by the definition of nonzero_helper
}
// </vc-code>
