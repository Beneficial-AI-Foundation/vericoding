function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
function IsIn(s: seq<int>, x: int): bool
{
  exists i :: 0 <= i < |s| && s[i] == x
}
// </vc-helpers>

// <vc-spec>
method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var seen: set<int> := {};
  result := [];
  for i := 0 to |a| - 1
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |result| ==> count_rec(a, result[j]) == 1
    invariant forall x_val :: x_val in seen <==> IsIn(result, x_val)
    invariant forall x_val :: x_val in seen ==> count_rec(a, x_val) == 1
    invariant forall k :: 0 <= k < |result| ==> forall m :: 0 <= m < k ==> result[k] != result[m]
    invariant forall k :: 0 <= k < i ==> count_rec(a,a[k]) == 1 ==> a[k] in seen
    invariant forall k :: 0 <= k < i ==> (count_rec(a, a[k]) == 1 <==> a[k] in seen)
  {
    if !(a[i] in seen) {
      if count_rec(a, a[i]) == 1 {
        result := result + [a[i]];
        seen := seen + {a[i]};
      }
    }
  }
}
// </vc-code>

method count(a: seq<int>, x: int) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
  // post-conditions-end
{
  assume{:axiom} false;
}