function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
lemma count_rec_property(a: seq<int>, x: int)
  ensures count_rec(a, x) == |set i | 0 <= i < |a| && a[i] == x|
{
  if |a| == 0 {
    assert a == [];
    assert (set i | 0 <= i < |a| && a[i] == x) == {};
  } else {
    count_rec_property(a[1..], x);
    var tail_set := set i | 0 <= i < |a[1..]| && a[1..][i] == x;
    var full_set := set i | 0 <= i < |a| && a[i] == x;
    var shifted_tail_set := set i | 1 <= i < |a| && a[i] == x;
    
    // Key insight: tail_set corresponds to shifted_tail_set
    assert forall j :: j in tail_set <==> (j+1) in shifted_tail_set;
    assert |tail_set| == |shifted_tail_set|;
    
    if a[0] == x {
      assert full_set == {0} + shifted_tail_set;
      assert 0 !in shifted_tail_set;
      assert |full_set| == 1 + |shifted_tail_set|;
      assert |full_set| == 1 + |tail_set|;
    } else {
      assert full_set == shifted_tail_set;
      assert |full_set| == |shifted_tail_set|;
      assert |full_set| == |tail_set|;
    }
  }
}

predicate all_unique(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]
}

lemma count_rec_monotonic(a: seq<int>, x: int, i: int)
  requires 0 <= i <= |a|
  ensures count_rec(a[..i], x) <= count_rec(a, x)
{
  count_rec_property(a[..i], x);
  count_rec_property(a, x);
  assert (set j | 0 <= j < i && a[j] == x) <= (set j | 0 <= j < |a| && a[j] == x);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method remove_duplicates(a: seq<int>) returns (result: seq<int>)
Process input. Requires: the condition holds for all values. Ensures: the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  ensures all_unique(result)
  ensures forall x :: x in result <==> x in a
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant all_unique(result)
    invariant forall x :: x in result ==> x in a[..i]
    invariant forall x :: x in a[..i] ==> (x in result <==> (exists j :: 0 <= j < i && a[j] == x))
  {
    if a[i] !in result {
      result := result + [a[i]];
    }
    i := i + 1;
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