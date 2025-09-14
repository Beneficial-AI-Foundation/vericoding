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
lemma count_rec_eq_set(a: seq<int>, x: int)
  ensures count_rec(a, x) == |set i | 0 <= i < |a| && a[i] == x|
  decreases |a|
{
  if |a| == 0 {
    // Both sides are 0 for empty sequence
  } else {
    // Inductive hypothesis on the tail
    count_rec_eq_set(a[1..], x);
    if a[0] == x {
      // By definition of count_rec
      assert count_rec(a, x) == count_rec(a[1..], x) + 1;
      // By IH
      assert count_rec(a, x) == |set i | 0 <= i < |a|-1 && a[1 + i] == x| + 1;
      // The set of indices for whole sequence equals the tail's set shifted by +1,
      // plus the 0 index when a[0]==x
      assert |set i | 0 <= i < |a| && a[i] == x| == |set i | 0 <= i < |a|-1 && a[1 + i] == x| + 1;
    } else {
      assert count_rec(a, x) == count_rec(a[1..], x);
      assert count_rec(a, x) == |set i | 0 <= i < |a|-1 && a[1 + i] == x|;
      assert |set i | 0 <= i < |a| && a[i] == x| == |set i | 0 <= i < |a|-1 && a[1 + i] == x|;
    }
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
  var i := 0;
  cnt := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant cnt == count_rec(a[..i], x)
  {
    if a[i] == x {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  // At loop exit i == |a|, so cnt == count_rec(a, x)
  assert cnt == count_rec(a, x);
  count_rec_eq_set(a, x);
  assert cnt == |set j | 0 <= j < |a| && a[j] == x|;
}
// </vc-code>

