function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
// Empty, no additional helpers needed
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
  var res: seq<int> := [];
  var seen: set<int> := {};
  for i := 0 to |a|
    invariant |res| == |seen|
    invariant forall x :: x in seen ==> count_rec(a, x) == 1 && exists j :: 0 <= j < i && a[j] == x
    invariant forall j :: 0 <= j < i && count_rec(a, a[j]) == 1 ==> a[j] in seen
    invariant forall j :: 0 <= j < |res| ==> count_rec(a, res[j]) == 1
  {
    if a[i] !in seen && count_rec(a, a[i]) == 1 {
      res := res + [a[i]];
      seen := seen + {a[i]};
    }
  }
  result := res;
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