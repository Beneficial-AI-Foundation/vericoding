// <vc-preamble>
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The type parameter `T(==)` is correct as it implies that `T` supports equality, necessary to compare multisets. */
predicate IsPermutation<T(==)>(s1: seq<T>, s2: seq<T>) { multiset(s1) == multiset(s2) }
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed array indexing issues in the loop invariants by adding checks for valid indices based on 'i' and 'j'. Updated `a` in invariants to refer to the current state of a since `a` is a value type. */
  var a := s;
  var n := |a|;

  for i := 0 to n-1
    invariant 0 <= i <= n
    invariant IsPermutation(s, a)
    invariant forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
    invariant forall k :: i <= k < n ==> (forall l :: 0 <= l < i ==> a[l] <= a[k])
  {

    var min_idx := i;
    for j := i + 1 to n-1
      invariant i < j <= n
      invariant i <= min_idx < j
      invariant forall k :: i <= k < j ==> a[min_idx] <= a[k]
    {
      if a[j] < a[min_idx] {
        min_idx := j;
      }
    }
    if min_idx != i {
      // Swap a[i] and a[min_idx]
      var temp := a[i];
      a := a[i := a[min_idx]];
      a := a[min_idx := temp];
    }
  }
  sorted := a;
}
// </vc-code>
