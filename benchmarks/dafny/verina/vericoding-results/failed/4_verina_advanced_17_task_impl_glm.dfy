// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(a: array<int>, low: int, high: int)
    reads a
    requires 0 <= low <= high <= a.Length
{
    forall i, j :: low <= i < j < high ==> a[i] <= a[j]
}

/* helper modified by LLM (iteration 2): added helper predicate for insertion sort */
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
  /* code modified by LLM (iteration 2): fixed insertion sort implementation */
  result := new int[l.Length];
  if l.Length == 0 {
    return;
  }
  
  // Initialize result with first element
  result[0] := l[0];
  
  var i := 1;
  while i < l.Length
    invariant 1 <= i <= l.Length
    invariant multiset(result[..i]) == multiset(l[..i])
    invariant IsSorted(result, 0, i)
  {
    var key := l[i];
    var j := i;
    
    // Shift elements greater than key to the right
    while j > 0 && result[j-1] > key
      invariant 0 <= j <= i
      invariant IsSorted(result, 0, j)
      invariant IsSorted(result, j, i)
      invariant forall k :: 0 <= k < j ==> result[k] <= key
      invariant multiset(result[..i]) == multiset(l[..i-1]) + multiset([key])
    {
      result[j] := result[j-1];
      j := j - 1;
    }
    
    result[j] := key;
    i := i + 1;
  }
}
// </vc-code>
