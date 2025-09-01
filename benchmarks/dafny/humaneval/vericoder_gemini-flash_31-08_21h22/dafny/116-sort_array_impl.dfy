function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
function popcount_seq(s: seq<nat>): seq<nat> {
  if |s| == 0 then []
  else [popcount(s[0])] + popcount_seq(s[1..])
}

predicate IsPermutation<T>(s1: seq<T>, s2: seq<T>) {
  multiset(s1) == multiset(s2)
}
  
method InsertionSort<T>(a: seq<T>, less: (T, T) -> bool) returns (b: seq<T>)
  ensures IsPermutation(a, b)
  ensures forall i, j :: 0 <= i < j < |b| ==> less(b[i], b[j]) || b[i] == b[j] // Changed <= to <, added `|| b[i] == b[j]`
{
  b := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant IsPermutation(a[..i], b)
    invariant forall x, y :: 0 <= x < y < |b| ==> less(b[x], b[y]) || b[x] == b[y] // Changed <= to <, added `|| b[x] == b[y]`
  {
    var x := a[i];
    var j := i;
    var b_old := b; // Store the old value of b before modification
    while j > 0 && less(x, b_old[j-1]) // Use b_old for the comparison
      invariant 0 < j <= i
      invariant forall k :: j <= k < i ==> b[k] == b_old[k-1] // Adjusted invariant: b[k] is the shifted element from b_old
      invariant forall k :: 0 <= k < j ==> b[k] == b_old[k] // Remaining elements are unchanged in b
      invariant forall k :: i <= k < |b_old| ==> b[k] == b_old[k] // Elements beyond i are unchanged
      invariant multiset(b[..i]) == multiset(b_old[..i]) // The elements up to i are a permutation
      invariant forall m, n :: 0 <= m < n < |b| ==> less(b[m], b[n]) || b[m] == b[n] // Added invariant for sortedness
      decreasing j
    {
      b := b_old[..j-1] + [b_old[j-1]] + b_old[j..]; // Shift element to the right
      j := j - 1;
      b_old := b; // Update b_old for the next iteration
    }
    b := b[..j] + [x] + b[j..i];
  }
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  function less_than_popcount(x: nat, y: nat): bool {
    (popcount(x) <= popcount(y))
  }
  sorted := InsertionSort(s, less_than_popcount);
}
// </vc-code>

