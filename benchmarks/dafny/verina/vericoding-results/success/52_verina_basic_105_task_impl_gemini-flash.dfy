// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed 'return' keyword as it is not used directly in Dafny function bodies. */
function ArrayProductHelper(a_i: int, b_i: int): int { a_i * b_i }
// </vc-helpers>

// <vc-spec>
method ArrayProduct(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] * b[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Changed array initialization to sequence, and then filled it using a while loop. Removed the unnecessary return statement. */
{
    var n := |a|;
    var res_seq: seq<int> := [];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |res_seq| == i
        invariant forall k :: 0 <= k < i ==> res_seq[k] == a[k] * b[k]
    {
        res_seq := res_seq + [ArrayProductHelper(a[i], b[i])];
        i := i + 1;
    }
    result := res_seq;
}
// </vc-code>
