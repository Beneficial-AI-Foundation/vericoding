// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Replaced 'result' with the function call in postconditions to fix compilation errors. */
function GenerateLucid(k: int): seq<int>
    requires k >= -1
    ensures forall i :: 0 <= i < |GenerateLucid(k)| ==> GenerateLucid(k)[i] % 3 == 0
    ensures forall i :: 0 <= i < |GenerateLucid(k)| ==> GenerateLucid(k)[i] <= k
    ensures forall i, j :: 0 <= i < j < |GenerateLucid(k)| ==> GenerateLucid(k)[i] < GenerateLucid(k)[j]
    decreases k
{
    if k < 0 then []
    else
        var prev := GenerateLucid(k - 1);
        if k % 3 == 0 then
            prev + [k]
        else
            prev
}
// </vc-helpers>

// <vc-spec>
method LucidNumbers(n: int) returns (lucid: seq<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
    ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): The implementation correctly calls the helper function. */
  lucid := GenerateLucid(n);
}
// </vc-code>
