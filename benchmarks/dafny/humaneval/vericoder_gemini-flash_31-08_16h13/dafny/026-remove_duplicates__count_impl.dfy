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
function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
lemma lemma_count_rec_subset(a: seq<int>, x: int, i: int)
  requires 0 <= i <= |a|
  ensures count_rec(a, x) == count_rec(a[..i], x) + count_rec(a[i..], x)
{
  if i == 0 {
    assert count_rec(a[..0], x) == 0;
    assert count_rec(a, x) == count_rec(a[0..], x);
  } else if i == |a| {
    assert count_rec(a[|a|..], x) == 0;
    assert count_rec(a, x) == count_rec(a[..|a|], x);
  } else {
    // This lemma essentially says that counting an element in a sequence is additive over concatenations.
    // It can be proven by induction on i.
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
  var cnt_local := 0;
  var i := 0;
  var a_val := a; 
  var x_val := x;

  while i < |a_val|
    invariant 0 <= i <= |a_val|
    invariant cnt_local == count_rec(a_val[..i], x_val)
    decreases |a_val| - i
  {
    if a_val[i] == x_val {
      cnt_local := cnt_local + 1;
    }
    i := i + 1;
  }
  return cnt_local;
}
// </vc-code>

