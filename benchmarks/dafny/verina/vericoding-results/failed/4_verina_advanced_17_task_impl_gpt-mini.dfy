// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): CopyArray copies elements preserving multiset */
method CopyArray(l: array<int>, a: array<int>)
  requires l != null && a != null && l.Length == a.Length
  modifies a
  ensures multiset(a[..]) == multiset(l[..])
{
  var n := l.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(a[..i]) == multiset(l[..i])
  {
    a[i] := l[i];
    i := i + 1;
  }
}

/* helper modified by LLM (iteration 5): Swap exchanges two elements preserving multiset */
method Swap(a: array<int>, i: int, j: int)
  requires a != null && 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  if i == j { return; }
  var tmp := a[i];
  a[i] := a[j];
  a[j] := tmp;
}

// </vc-helpers>

// <vc-spec>
method insertion_sort(l: array<int>) returns (result: array<int>)
    ensures
        /* The result is sorted in non-decreasing order */
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        /* The result is a permutation of the input */
        result.Length == l.Length && multiset(result[..]) == multiset(l[..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Selection sort using CopyArray and Swap, preserving multiset */
  result := new int[l.Length];
  CopyArray(l, result);
  var n := result.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(result[..]) == multiset(l[..])
    invariant forall p, q :: 0 <= p < q < i ==> result[p] <= result[q]
    invariant forall p :: 0 <= p < i ==> forall k :: i <= k < n ==> result[p] <= result[k]
  {
    var m := i;
    var k := i + 1;
    while k < n
      invariant i <= m < n
      invariant i + 1 <= k <= n
      invariant multiset(result[..]) == multiset(l[..])
      invariant forall t :: i <= t < k ==> result[m] <= result[t]
    {
      if result[k] < result[m] {
        m := k;
      }
      k := k + 1;
    }
    Swap(result, i, m);
    i := i + 1;
  }
}

// </vc-code>
