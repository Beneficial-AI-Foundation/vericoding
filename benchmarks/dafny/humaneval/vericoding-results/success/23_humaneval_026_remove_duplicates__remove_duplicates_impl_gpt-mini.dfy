// <vc-preamble>
function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
function IsElementUnique(a: seq<int>, x: int): bool { count_rec(a, x) == 1 }
// </vc-helpers>

// <vc-spec>
method remove_duplicates(a: seq<int>) returns (result: seq<int>)

  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1

  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
// </vc-spec>
// <vc-code>
{
  var r := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |r| <= i
    invariant forall j :: 0 <= j < |r| ==> count_rec(a, r[j]) == 1
    invariant forall k :: 0 <= k < i ==> (a[k] in r <==> count_rec(a, a[k]) == 1)
  {
    if count_rec(a, a[i]) == 1 {
      r := r + [a[i]];
    }
    i := i + 1;
  }
  result := r;
}
// </vc-code>
