function verifyNeg(a: array<int>, idx: int) : nat
reads a
requires 0 <= idx <= a.Length
{
    if idx == 0 then 0 
    else verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}

// <vc-helpers>
lemma VerifyNegLemma(a: array<int>, idx: int)
    requires 0 <= idx <= a.Length
    ensures verifyNeg(a, idx) == (if idx == 0 then 0 else verifyNeg(a, idx - 1) + (if a[idx-1] < 0 then 1 else 0))
{
    // This lemma is simply restating the definition of verifyNeg,
    // which Dafny's verifier can often handle automatically by inlining.
    // However, explicitly stating it can sometimes help in complex inductions.
}
// </vc-helpers>

// <vc-spec>
method CountNeg(a: array<int>) returns (cnt: nat) 
ensures cnt == verifyNeg(a, a.Length)
// </vc-spec>
// <vc-code>
{
    var current_cnt := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant current_cnt == verifyNeg(a, i)
    {
        if a[i] < 0 {
            current_cnt := current_cnt + 1;
        }
        i := i + 1;
    }
    return current_cnt;
}
// </vc-code>

