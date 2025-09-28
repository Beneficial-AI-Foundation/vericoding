// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added requires clause to ensure input sorted is sorted for verifying postconditions */
method insert(el: nat, sorted: seq<nat>) returns (result: seq<nat>)
  decreases |sorted|
  requires forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures forall i, j :: 0 <= i < j < |result| ==> popcount(result[i]) <= popcount(result[j])
  ensures multiset(result) == multiset(sorted) + multiset([el])
  ensures |result| == |sorted| + 1
{
  var prefix := 0;
  while prefix < |sorted| && popcount(el) > popcount(sorted[prefix])
    invariant prefix <= |sorted|
    invariant forall i, j :: 0 <= i < j < prefix ==> popcount(sorted[i]) <= popcount(sorted[j])
    invariant forall i :: 0 <= i < prefix ==> popcount(sorted[i]) <= popcount(el)
  {
    prefix := prefix + 1;
  }
  result := sorted[..prefix] + [el] + sorted[prefix..];
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): retained insertion sort implementation using corrected insert helper */
  sorted := [];
  var i : int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall x, y :: 0 <= x < y < |sorted| ==> popcount(sorted[x]) <= popcount(sorted[y])
    invariant multiset(sorted) == multiset(s[..i])
    invariant |sorted| == i
  {
    sorted := insert(s[i], sorted);
    i := i + 1;
  }
}
// </vc-code>
