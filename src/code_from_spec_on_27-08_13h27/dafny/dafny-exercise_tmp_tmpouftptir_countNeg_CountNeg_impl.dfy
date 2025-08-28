function verifyNeg(a: array<int>, idx: int) : nat
reads a
requires 0 <= idx <= a.Length
{
    if idx == 0 then 0 
    else verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}

// <vc-helpers>
lemma VerifyNegCorrect(a: array<int>, idx: int)
  requires 0 <= idx <= a.Length
  ensures verifyNeg(a, idx) == CountNegUpTo(a, idx)
{
  if idx == 0 {
    assert verifyNeg(a, 0) == 0;
    assert CountNegUpTo(a, 0) == 0;
  } else {
    VerifyNegCorrect(a, idx - 1);
    assert verifyNeg(a, idx) == verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0);
    assert CountNegUpTo(a, idx) == CountNegUpTo(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0);
  }
}

function CountNegUpTo(a: array<int>, idx: int): nat
  reads a
  requires 0 <= idx <= a.Length
{
  if idx == 0 then 0
  else CountNegUpTo(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CountNeg(a: array<int>) returns (cnt: nat) 
ensures cnt == verifyNeg(a, a.Length)
// </vc-spec>
// </vc-spec>

// <vc-code>
method CountNegImpl(a: array<int>) returns (cnt: nat)
  ensures cnt == verifyNeg(a, a.Length)
{
  cnt := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant cnt == verifyNeg(a, i)
  {
    if a[i] < 0 {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  VerifyNegCorrect(a, a.Length);
}
// </vc-code>
