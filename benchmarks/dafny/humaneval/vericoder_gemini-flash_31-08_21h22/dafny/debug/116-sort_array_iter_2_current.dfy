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
  ensures forall i, j :: 0 <= i < j < |b| ==> less(b[i], b[j]) || b[i] == b[j]
{
  b := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant IsPermutation(a[..i], b)
    invariant forall x, y :: 0 <= x < y < |b| ==> less(b[x], b[y]) || b[x] == b[y]
  {
    var j := i;
    while j > 0 && less(a[i], b[j-1])
      invariant 0 < j <= i
      invariant IsPermutation(a[..i], b[..j] + b[j-1..i-1] + [a[i]] + b[i+1..]) // A specific permutation.
      invariant forall x, y :: 0 <= x < y < |b| ==> less(b[x], b[y]) || b[x] == b[y]
      decreasing j
    {
      j := j - 1;
    }
    b := b[..j] + [a[i]] + b[j..];
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
    popcount(x) <= popcount(y)
  }
  sorted := InsertionSort(s, less_than_popcount);
}
// </vc-code>

