

// <vc-helpers>
lemma EvenDouble(len: int)
  requires len % 2 == 0
  ensures len == 2*(len/2)
{
  // Use integer division properties
  assert len == 2*(len/2);
}

lemma TwoTimesBound(i: int, n: int)
  requires 0 <= i < n
  ensures 2*i + 1 < 2*n
{
  assert i <= n - 1;
  calc {
    2*i + 1;
    <= 2*(n - 1) + 1;
    < 2*n;
  }
}

lemma TwoTimesBoundArray(i: int, a: array<int>)
  requires a != null
  requires a.Length % 2 == 0
  requires 0 <= i < a.Length / 2
  ensures 2*i + 1 < a.Length
{
  EvenDouble(a.Length);
  assert a.Length == 2*(a.Length / 2);
  assert i <= a.Length/2 - 1;
  calc {
    2*i + 1;
    <= 2*(a.Length/2 - 1) + 1;
    == 2*(a.Length/2) - 1;
    == a.Length - 1;
    < a.Length;
  }
}
// </vc-helpers>

// <vc-spec>
method PairwiseAddition(a: array<int>) returns (result: array<int>)
    requires a != null
    requires a.Length % 2 == 0
    ensures result != null
    ensures result.Length == a.Length / 2
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[2*i] + a[2*i + 1]
// </vc-spec>
// <vc-code>
{
  // Defensive ghost assertions to make intent explicit to the verifier
  ghost assert a != null;
  result := new int[a.Length / 2];
  // a.Length is even by precondition; relate it to result.Length
  EvenDouble(a.Length);
  assert a.Length == 2*(a.Length / 2);
  assert a.Length == 2*result.Length;
  var i := 0;
  while i < result.Length
    invariant 0 <= i <= result.Length
    invariant forall k :: 0 <= k < i ==> result[k] == a[2*k] + a[2*k + 1]
  {
    TwoTimesBoundArray(i, a);
    assert 2*i + 1 < a.Length;
    result[i] := a[2*i] + a[2*i + 1];
    i := i + 1;
  }
  // result is freshly allocated non-null by construction
  ghost assert result != null;
  return result;
}
// </vc-code>

