// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapFirstAndLast(a: seq<int>) returns (result: seq<int>)
    requires |a| > 0
    ensures |result| == |a|
    ensures result[0] == a[|a| - 1]
    ensures result[|result| - 1] == a[0]
    ensures forall i :: 1 <= i < |result| - 1 ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fix type errors by using sequence operations for `result` and handling the base case of `len == 1` correctly */
{
    var len := |a|;
    if len == 1 {
        return a;
    }

    var temp_res: seq<int> := a;
    temp_res := temp_res[0 := a[len - 1]];
    temp_res := temp_res[len - 1 := a[0]];
    result := temp_res;
    return result;
}
// </vc-code>
