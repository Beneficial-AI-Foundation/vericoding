function verifyNeg(a: array<int>, idx: int) : nat
reads a
requires 0 <= idx <= a.Length
{
    if idx == 0 then 0 
    else verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method CountNeg(a: array<int>) returns (cnt: nat) 
ensures cnt == verifyNeg(a, a.Length)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  cnt := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant cnt == verifyNeg(a, i)
    decreases a.Length - i
  {
    var add: nat := if a[i] < 0 then 1 else 0;
    // unfold the definition of verifyNeg for i+1 (i < a.Length ensures i+1 > 0)
    assert verifyNeg(a, i + 1) == verifyNeg(a, i) + (if a[i] < 0 then 1 else 0);
    cnt := cnt + add;
    i := i + 1;
    assert cnt == verifyNeg(a, i);
  }
}
// </vc-code>

