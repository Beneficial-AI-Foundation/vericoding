// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: array<int>)
    requires a.Length >= 1
    ensures forall i :: 0 <= i < result.Length ==> InArray(a[..], result[i])
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added invariants to the copying loop to ensure result matches resultSeq */
  var resultSeq: seq<int> := [];
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < |resultSeq| ==> exists j :: 0 <= j < i && a[j] == resultSeq[k]
    invariant forall k, m :: 0 <= k < m < |resultSeq| ==> resultSeq[k] != resultSeq[m]
  {
    var found: bool := false;
    var j: int := 0;
    while j < |resultSeq|
      invariant 0 <= j <= |resultSeq|
      invariant !found ==> forall m :: 0 <= m < j ==> resultSeq[m] != a[i]
    {
      if resultSeq[j] == a[i] {
        found := true;
        break;
      }
      j := j + 1;
    }
    if !found {
      resultSeq := resultSeq + [a[i]];
    }
    i := i + 1;
  }
  result := new int[|resultSeq|] (_ => 0);
  var k: int := 0;
  while k < |resultSeq|
    invariant 0 <= k <= |resultSeq|
    invariant forall m :: 0 <= m < k ==> result[m] == resultSeq[m]
  {
    result[k] := resultSeq[k];
    k := k + 1;
  }
  assert result.Length == |resultSeq|;
  assert forall k :: 0 <= k < |resultSeq| ==> result[k] == resultSeq[k];
}
// </vc-code>
