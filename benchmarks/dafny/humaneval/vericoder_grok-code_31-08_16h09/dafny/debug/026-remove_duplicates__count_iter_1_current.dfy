function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function count_alt(a: seq<int>, x: int): (c: int)
  ensures c == |set i | 0 <= i < |a| && a[i] == x :: i|
{
  |set i: int | 0 <= i < |a| && a[i] == x :: i|
}
lemma count_rec_eq_count_alt(a: seq<int>, x: int)
  ensures count_rec(a, x) == count_alt(a, x)
{
  if |a| == 0 {
    assert count_rec(a, x) == 0;
    assert count_alt(a, x) == 0;
  } else {
    count_rec_eq_count_alt(a[1..], x);
    assert count_rec(a, x) == count_rec(a[1..], x) + (if a[0] == x then 1 else 0);
    assert count_alt(a, x) == count_alt(a[1..], x) + (if a[0] == x then 1 else 0);
  }
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>, x: int) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := count_rec(a, x);
  count_rec_eq_count_alt(a, x);
}
// </vc-code>

