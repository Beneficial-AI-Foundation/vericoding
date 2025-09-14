// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error in predicate by correcting the body expression */
predicate IsSorted(a: array<int>)
  reads a
  ensures IsSorted(a) <==> forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{ forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j] }
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
  /* code modified by LLM (iteration 5): fixed typo 'Longth' to 'Length' */
  result := new int[l.Length];
  var i := 0;
  while i < l.Length
  {
    result[i] := l[i];
    i := i + 1;
  }
  i := 1;
  while i < result.Length
    invariant multiset(result[..]) == multiset(l[..])
    invariant forall p, q :: 0 <= p < q < i ==> result[p] <= result[q]
  {
    var key := result[i];
    var j := i - 1;
    while j >= 0 && result[j] > key
    {
      result[j+1] := result[j];
      j := j - 1;
    }
    result[j+1] := key;
    i := i + 1;
  }
}
// </vc-code>
