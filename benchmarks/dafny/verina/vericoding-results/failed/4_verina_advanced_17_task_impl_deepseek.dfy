// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function array_copy(src: array<int>): (dest: array<int>)
  requires src != null
  ensures dest != null
  ensures dest.Length == src.Length
  ensures multiset(dest[..]) == multiset(src[..])
{
  /* helper modified by LLM (iteration 5): Fixed new array construction syntax */
  var copy := new int[](src.Length);
  var idx: int := 0;
  while idx < src.Length
    invariant 0 <= idx <= src.Length
    invariant forall k :: 0 <= k < idx ==> copy[k] == src[k]
    invariant multiset(copy[0..idx]) == multiset(src[0..idx])
  {
    copy[idx] := src[idx];
    idx := idx + 1;
  }
  copy
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
  /* code modified by LLM (iteration 5): Fixed insertion sort implementation with proper invariants */
  result := new int[l.Length];
  
  // Copy the array first
  var k: int := 0;
  while k < l.Length
    invariant 0 <= k <= l.Length
    invariant forall x :: 0 <= x < k ==> result[x] == l[x]
    invariant multiset(result[0..k]) == multiset(l[0..k])
  {
    result[k] := l[k];
    k := k + 1;
  }
  
  if result.Length > 0 {
    var i: int := 1;
    while i < result.Length
      invariant 1 <= i <= result.Length
      invariant forall x, y :: 0 <= x < y < i ==> result[x] <= result[y]
      invariant multiset(result[..]) == multiset(l[..])
    {
      var key: int := result[i];
      var j: int := i - 1;
      
      while j >= 0 && result[j] > key
        invariant -1 <= j < i
        invariant forall x, y :: 0 <= x < y < i && x != j+1 && y != j+1 ==> result[x] <= result[y]
        invariant forall x :: j+1 < x <= i ==> result[x] > key
        invariant multiset(result[..]) == multiset(l[..])
        decreases j + 1
      {
        result[j+1] := result[j];
        j := j - 1;
      }
      
      result[j+1] := key;
      i := i + 1;
    }
  }
}
// </vc-code>
