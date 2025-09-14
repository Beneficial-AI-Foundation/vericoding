// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

  predicate InArray(arr: array<int>, x: int)
    reads arr
  {
    exists k :: 0 <= k < arr.Length && arr[k] == x
  }

// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires 
        a.Length > 0 &&
        b.Length > 0
    ensures
        result == (exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j])
// </vc-spec>
// <vc-code>
{
  var index_a := 0;
  
  while index_a < a.Length
    invariant index_a <= a.Length
    invariant !(exists i, j :: 0 <= i < index_a && 0 <= j < b.Length && a[i] == b[j])
  {
    if InArray(b, a[index_a]) {
      result := true;
      return;
    }
    index_a := index_a + 1;
  }
  
  result := false;
}
// </vc-code>
