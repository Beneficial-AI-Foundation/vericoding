// <vc-preamble>
predicate AllNonzero(v: seq<int>)
{
    forall i :: 0 <= i < |v| ==> v[i] != 0
}
// </vc-preamble>

// <vc-helpers>
lemma AllNonzero_array(b: array<int>, i: int)
  requires 0 <= i < b.Length
  requires AllNonzero(b[..])
  ensures b[i] != 0
{
  assert b[..][i] != 0;
}

// </vc-helpers>

// <vc-spec>
method ModVec(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    requires AllNonzero(b[..])
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  var len := a.Length;
  var res := new int[len];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant res.Length == len
    invariant forall k :: 0 <= k < i ==> res[k] == a[k] % b[k]
  {
    AllNonzero_array(b, i);
    res[i] := a[i] % b[i];
    i := i + 1;
  }
  result := res;
}

// </vc-code>
