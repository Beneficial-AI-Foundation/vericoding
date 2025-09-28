// <vc-preamble>
function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method remove_duplicates(a: seq<int>) returns (result: seq<int>)

  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1

  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in result ==> count_rec(a, x) == 1
    invariant forall k :: 0 <= k < i ==> (count_rec(a, a[k]) == 1 ==> a[k] in result)
  {
    var current_element := a[i];
    if count_rec(a, current_element) == 1 {
      result := result + [current_element];
    }
    i := i + 1;
  }
}
// </vc-code>
