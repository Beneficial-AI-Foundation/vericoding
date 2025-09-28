// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): replaced loop invariants with standard insertion sort invariants to ensure sortedness and multiset preservation */
  result := new int[l.Length];
  if l.Length > 0 {
    for i := 0 to l.Length - 1 {
      result[i] := l[i];
    }
  }
  if result.Length > 1 {
    for i := 1 to result.Length - 1
      invariant 1 <= i <= result.Length
      invariant forall k, m :: 0 <= k < m < i ==> result[k] <= result[m]
      invariant multiset(result[..]) == multiset(l[..])
    {
      var key := result[i];
      var j := i - 1;
      while j >= 0 && result[j] > key
        invariant 0 <= j <= i - 1
        invariant forall k :: 0 <= k <= j ==> result[k] <= key
        invariant forall k :: j + 1 <= k < i ==> key <= result[k]
        invariant forall k, m :: 0 <= k < m <= j ==> result[k] <= result[m]
        invariant forall k, m :: j + 1 < k < m < i ==> result[k] <= result[m]
        invariant multiset(result[..]) == multiset(l[..])
      {
        result[j + 1] := result[j];
        j := j - 1;
      }
      result[j + 1] := key;
    }
  }
}
// </vc-code>
