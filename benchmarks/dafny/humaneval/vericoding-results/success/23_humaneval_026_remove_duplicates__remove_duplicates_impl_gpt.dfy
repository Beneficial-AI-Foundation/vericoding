// <vc-preamble>
function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
lemma CountEqualityForEqualArgs(a: seq<int>, x: int, y: int)
  requires x == y
  ensures count_rec(a, x) == count_rec(a, y)
{
}

lemma MemAppendRight(s: seq<int>, x: int)
  ensures x in s + [x]
{
}
// </vc-helpers>

// <vc-spec>
method remove_duplicates(a: seq<int>) returns (result: seq<int>)

  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1

  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := [];
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |result| ==> count_rec(a, result[j]) == 1
    invariant forall k :: 0 <= k < i ==> (count_rec(a, a[k]) == 1 ==> a[k] in result)
    invariant forall k :: 0 <= k < |result| ==> exists m :: 0 <= m < i && result[k] == a[m]
  {
    if count_rec(a, a[i]) == 1 {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
