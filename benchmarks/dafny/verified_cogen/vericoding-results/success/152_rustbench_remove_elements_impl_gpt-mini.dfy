// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): index implies InArray(seq,x) */
lemma IndexImpliesInArray(a: array<int>, p: int, x: int)
  requires 0 <= p < a.Length
  requires a[p] == x
  ensures InArray(a[..], x)
{
}

// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (c: array<int>)
    ensures forall k :: 0 <= k < c.Length ==> InArray(a[..], c[k]) && !InArray(b[..], c[k])
    ensures forall i, j :: 0 <= i < j < c.Length ==> c[i] != c[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): implement RemoveElements collecting unique elements from a that are not in b and prove postconditions */
  var temp := new int[a.Length];
  var m := 0;
  var idx := 0;
  while idx < a.Length
    invariant 0 <= m <= a.Length
    invariant 0 <= idx <= a.Length
    invariant m <= idx
    invariant forall k :: 0 <= k < m ==> InArray(a[..], temp[k]) && !InArray(b[..], temp[k])
    invariant forall i, j :: 0 <= i < j < m ==> temp[i] != temp[j]
    invariant forall k :: 0 <= k < m ==> exists p :: 0 <= p < idx && a[p] == temp[k]
  {
    var x := a[idx];
    if !InArray(b[..], x) {
      var found := false;
      var j := 0;
      while j < m
        invariant 0 <= j <= m
        invariant found == (exists k :: 0 <= k < j && temp[k] == x)
      {
        if temp[j] == x { found := true; }
        j := j + 1;
      }
      if !found {
        temp[m] := x;
        m := m + 1;
      }
    }
    idx := idx + 1;
  }
  c := new int[m];
  var k := 0;
  while k < m
    invariant 0 <= k <= m
    invariant forall i :: 0 <= i < k ==> c[i] == temp[i]
    invariant forall i, j :: 0 <= i < j < k ==> c[i] != c[j]
    invariant forall t :: 0 <= t < m ==> InArray(a[..], temp[t]) && !InArray(b[..], temp[t])
    invariant forall i, j :: 0 <= i < j < m ==> temp[i] != temp[j]
  {
    c[k] := temp[k];
    var i := 0;
    while i < k
      invariant 0 <= i <= k
      invariant forall t :: 0 <= t < i ==> c[t] != c[k]
    {
      assert c[i] == temp[i];
      assert temp[i] != temp[k];
      assert c[i] != temp[k];
      assert c[i] != c[k];
      i := i + 1;
    }
    assert InArray(a[..], c[k]) && !InArray(b[..], c[k]);
    k := k + 1;
  }
  assert forall t :: 0 <= t < m ==> InArray(a[..], c[t]) && !InArray(b[..], c[t]);
  assert forall i, j :: 0 <= i < j < m ==> c[i] != c[j];
}

// </vc-code>
