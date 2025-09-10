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
lemma set_prefix_card_inc(a: seq<int>, i: int, x: int)
  requires 0 <= i < |a|
  ensures |set j | 0 <= j < i+1 && a[j] == x :: j| == |set j | 0 <= j < i && a[j] == x :: j| + (if a[i] == x then 1 else 0)
{
  var prev := set j | 0 <= j < i && a[j] == x :: j;
  var next := set j | 0 <= j < i+1 && a[j] == x :: j;
  if a[i] == x {
    // Show next = prev ∪ {i}
    // (⊆) direction
    assert forall k :: (0 <= k < i+1 && a[k] == x) ==> (k in prev || k == i);
    // (⊇) direction
    assert forall k :: (k in prev || k == i) ==> (0 <= k < i+1 && a[k] == x);
    assert next == prev + {i};
    // i is not in prev
    assert !(i in prev);
    // Cardinality of union with a new element increases by 1
    assert |prev + {i}| == |prev| + 1;
    assert |next| == |prev| + 1;
  } else {
    // a[i] != x, so next == prev
    assert forall k :: (0 <= k < i+1 && a[k] == x) ==> (0 <= k < i && a[k] == x);
    assert forall k :: (0 <= k < i && a[k] == x) ==> (0 <= k < i+1 && a[k] == x);
    assert next == prev;
    assert |next| == |prev|;
  }
}

lemma count_rec_eq_set(a: seq<int>, x: int)
  ensures count_rec(a, x) == |set i | 0 <= i < |a| && a[i] == x :: i|
  decreases |a|
{
  if |a| == 0 {
    // both sides are 0
  } else {
    // IH on tail
    count_rec_eq_set(a[1..], x);
    var tailSet := set i | 0 <= i < |a[1..]| && a[1 + i] == x :: i;
    var fullSet := set i | 0 <= i < |a| && a[i] == x :: i;
    if a[0] == x {
      // fullSet = {0} ∪ {1+i | i in tailSet} i.e., prev ∪ {0}
      // Show membership equivalence
      assert forall k :: (0 <= k < |a| && a[k] == x) ==> (k == 0 || (1 <= k < |a| && a[k] == x));
      assert forall k :: (k == 0 || (1 <= k < |a| && a[k] == x)) ==> (0 <= k < |a| && a[k] == x);
      // Relate the 1.. range to tailSet
      assert forall k :: (1 <= k < |a| && a[k] == x) ==> ((k-1) in tailSet);
      assert forall k :: (k in tailSet) ==> (1 + k < |a| && a[1 + k] == x);
      // So fullSet = {0} + (set 1..) and set 1.. corresponds to tailSet
      assert fullSet == {0} + (set k | 0 <= k < |a[1..]| && a[1 + k] == x :: 1 + k);
      // cardinality then is 1 + |tailSet|
      assert |fullSet| == 1 + |tailSet|;
      // By definition of count_rec:
      assert count_rec(a, x) == count_rec(a[1..], x) + 1;
      // By IH
      assert count_rec(a, x) == |tailSet| + 1;
      assert count_rec(a, x) == |fullSet|;
    } else {
      // a[0] != x, so fullSet corresponds exactly to tailSet shifted
      assert forall k :: (0 <= k < |a| && a[k] == x) ==> (1 <= k < |a| && a[k] == x);
      assert forall k :: (1 <= k < |a| && a[k] == x) ==> (0 <= k-1 < |a[1..]| && a[1 + (k-1)] == x);
      assert fullSet == (set k | 0 <= k < |a[1..]| && a[1 + k] == x :: 1 + k);
      // cardinalities equal
      assert |fullSet| == |tailSet|;
      // By definition of count_rec:
      assert count_rec(a, x) == count_rec(a[1..], x);
      // By IH
      assert count_rec(a, x) == |tailSet|;
      assert count_rec(a, x) == |fullSet|;
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
    invariant cnt == |set j | 0 <= j < i && a[j] == x :: j|
  {
    if a[i] == x {
      cnt := cnt + 1;
    }
    // After possibly incrementing cnt, relate it to the set up to i+1
    set_prefix_card_inc(a, i, x);
    assert cnt == |set j | 0 <= j < i+1 && a[j] == x :: j|;
    i := i + 1;
  }
  assert i == |a|;
  assert cnt == |set j | 0 <= j < |a| && a[j] == x :: j|;
  count_rec_eq_set(a, x);
  assert cnt == count_rec(a, x);
}
// </vc-code>

