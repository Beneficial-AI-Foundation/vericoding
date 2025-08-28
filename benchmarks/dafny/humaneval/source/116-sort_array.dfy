function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// pure-end
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  // impl-start
  var popcounts := [];
  var pi := 0;
  while pi < |s|
    // invariants-start
    invariant 0 <= pi <= |s|
    invariant |popcounts| == pi
    invariant forall i :: 0 <= i < pi ==> popcounts[i] == popcount(s[i])
    // invariants-end
  {
    popcounts := popcounts + [popcount(s[pi])];
    pi := pi + 1;
  }

  sorted := s;
  var i := 0;
  while i < |sorted|
    // invariants-start
    invariant 0 <= i <= |sorted|
    invariant |popcounts| == |sorted|
    invariant forall i :: 0 <= i < |sorted| ==> popcounts[i] == popcount(sorted[i])
    invariant forall j, k :: 0 <= j < k < i ==> popcount(sorted[j]) <= popcount(sorted[k])
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> popcount(sorted[j]) <= popcount(sorted[k])
    invariant |sorted| == |s|
    // invariants-end
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
      // invariants-start
      invariant i <= minIndex < j <= |sorted|
      invariant forall k :: i <= k < j ==> popcount(sorted[minIndex]) <= popcount(sorted[k])
      // invariants-end
    {
      if popcounts[j] < popcounts[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];

      var temp2 := popcounts[i];
      popcounts := popcounts[i := popcounts[minIndex]][minIndex := temp2];
    }
    i := i + 1;
  }
  // impl-end
}
