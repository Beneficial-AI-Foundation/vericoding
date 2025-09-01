function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
function findInsertIndex(x: nat, sorted: seq<nat>): nat
  requires forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures 0 <= findInsertIndex(x, sorted) <= |sorted|
  ensures forall i :: 0 <= i < findInsertIndex(x, sorted) ==> popcount(sorted[i]) < popcount(x)
  ensures findInsertIndex(x, sorted) < |sorted| ==> popcount(x) <= popcount(sorted[findInsertIndex(x, sorted)])
  decreases |sorted|
{
  if |sorted| == 0 then 0
  else 
    if popcount(x) <= popcount(sorted[0]) then 0
    else 1 + findInsertIndex(x, sorted[1..])
}

function insert(x: nat, sorted: seq<nat>): seq<nat>
  requires forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures forall i, j :: 0 <= i < j < |insert(x, sorted)| ==> popcount(insert(x, sorted)[i]) <= popcount(insert(x, sorted)[j])
  ensures multiset(insert(x, sorted)) == multiset([x] + sorted)
{
  var idx := findInsertIndex(x, sorted);
  sorted[0..idx] + [x] + sorted[idx..]
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
  sorted := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant forall j, k :: 0 <= j < k < |sorted| ==> popcount(sorted[j]) <= popcount(sorted[k])
    invariant multiset(sorted) == multiset(s[0..i])
  {
    sorted := insert(s[i], sorted);
  }
}
// </vc-code>

