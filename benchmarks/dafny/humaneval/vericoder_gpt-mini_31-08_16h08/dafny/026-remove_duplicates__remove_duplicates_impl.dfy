function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
// (No helpers needed)
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
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> 0 <= j < |a| && ((a[j] in res) <==> count_rec(a, a[j]) == 1)
    invariant forall k :: 0 <= k < |res| ==> count_rec(a, res[k]) == 1
    invariant forall p, q :: 0 <= p < |res| && 0 <= q < |res| && p < q ==> res[p] != res[q]
  {
    var ai := a[i];
    var wasIn := ai in res;
    if count_rec(a, ai) == 1 && !wasIn {
      res := res + [ai];
    }
    if count_rec(a, ai) == 1 {
      assert ai in res;
    } else {
      assert !(ai in res);
    }
    i := i + 1;
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