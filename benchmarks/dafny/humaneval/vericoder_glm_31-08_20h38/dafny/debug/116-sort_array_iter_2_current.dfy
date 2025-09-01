function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
function insert(x: nat, sorted: seq<nat>): seq<nat>
  requires forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures forall i, j :: 0 <= i < j < |insert(x, sorted)| ==> popcount(insert(x, sorted)[i]) <= popcount(insert(x, sorted)[j])
  ensures multiset(insert(x, sorted)) == multiset([x] + sorted)
  decreases |sorted|
{
  if |sorted| == 0 then [x]
  else
    if popcount(x) <= popcount(sorted[0]) then [x] + sorted
    else [sorted[0]] + insert(x, sorted[1..])
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
  var sorted := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall j, k :: 0 <= j < k < |sorted| ==> popcount(sorted[j]) <= popcount(sorted[k])
    invariant multiset(sorted) == multiset(s[0..i])
  {
    sorted := insert(s[i], sorted);
  }
  sorted;
}
// </vc-code>

