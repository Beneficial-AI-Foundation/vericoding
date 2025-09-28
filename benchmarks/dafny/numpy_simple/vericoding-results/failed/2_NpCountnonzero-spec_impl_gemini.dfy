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
/* helper modified by LLM (iteration 4): [rewrote relation lemma to more closely match function definition] */
lemma LemmaNonZeroHelperBound(s: seq<real>)
  ensures nonzero_helper(s) <= |s|
  decreases |s|
{
  if |s| > 0 {
    LemmaNonZeroHelperBound(s[1..]);
  }
}

lemma LemmaNonZeroHelperRelation(s: seq<real>)
  requires |s| > 0
  ensures nonzero_helper(s) == (if s[0] == 0.0 then nonzero_helper(s[1..]) else nonzero_helper(s[1..]) + 1)
{
  // This follows directly from the definition of nonzero_helper.
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
{
    /* code modified by LLM (iteration 5): [re-instated lemma call to guide verifier] */
    result := 0;
    var i: nat := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant result + nonzero_helper(arr[i..]) == nonzero_helper(arr[..])
    {
        LemmaNonZeroHelperBound(arr[i..]);
        if arr.Length - i > 0 {
            LemmaNonZeroHelperRelation(arr[i..]);
        }
        if arr[i] != 0.0 {
            result := result + 1;
        }
        i := i + 1;
    }

    if arr.Length > 0 {
        LemmaNonZeroHelperRelation(arr[..]);
    }
    LemmaNonZeroHelperBound(arr[..]);
    assert result == nonzero_helper(arr[..]);
}
// </vc-code>
