function verifyNeg(a: array<int>, idx: int) : nat
reads a
requires 0 <= idx <= a.Length
{
    if idx == 0 then 0 
    else verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}

// <vc-helpers>
lemma verifyNeg_step(a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures verifyNeg(a, i + 1) == verifyNeg(a, i) + (if a[i] < 0 then 1 else 0)
{
  assert 0 <= i + 1 <= a.Length;
  assert i + 1 != 0;
  assert (i + 1) - 1 == i;
  assert verifyNeg(a, i + 1) == (if i + 1 == 0 then 0 else verifyNeg(a, (i + 1) - 1) + (if a[(i + 1) - 1] < 0 then 1 else 0));
}
// </vc-helpers>

// <vc-spec>
method CountNeg(a: array<int>) returns (cnt: nat) 
ensures cnt == verifyNeg(a, a.Length)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  cnt := 0;
  while i < a.Length
    invariant i <= a.Length
    invariant cnt == verifyNeg(a, i)
    decreases a.Length - i
  {
    assert 0 <= i < a.Length;
    var i0 := i;
    var c0 := cnt;
    if a[i0] < 0 {
      cnt := cnt + 1;
    }
    assert c0 == verifyNeg(a, i0);
    assert cnt == c0 + (if a[i0] < 0 then 1 else 0);
    verifyNeg_step(a, i0);
    assert cnt == verifyNeg(a, i0 + 1);
    i := i0 + 1;
    assert cnt == verifyNeg(a, i);
  }
}
// </vc-code>

