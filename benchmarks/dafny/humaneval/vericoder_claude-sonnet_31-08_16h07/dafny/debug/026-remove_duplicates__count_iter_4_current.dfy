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
lemma count_rec_properties(a: seq<int>, x: int)
  ensures count_rec(a, x) == |set i | 0 <= i < |a| && a[i] == x|
{
  if |a| == 0 {
    assert a == [];
    assert (set i | 0 <= i < |a| && a[i] == x) == {};
  } else {
    var tail := a[1..];
    count_rec_properties(tail, x);
    
    var tail_indices := set i | 0 <= i < |tail| && tail[i] == x;
    var shifted_indices := set i | 1 <= i < |a| && a[i] == x;
    var full_indices := set i | 0 <= i < |a| && a[i] == x;
    
    // Prove bijection between tail_indices and shifted_indices
    forall i | i in tail_indices
      ensures i + 1 in shifted_indices
    {
      assert 0 <= i < |tail|;
      assert tail[i] == x;
      assert 1 <= i + 1 < |a|;
      assert a[i + 1] == tail[i] == x;
    }
    
    forall i | i in shifted_indices
      ensures i - 1 in tail_indices
    {
      assert 1 <= i < |a|;
      assert a[i] == x;
      assert 0 <= i - 1 < |tail|;
      assert tail[i - 1] == a[i] == x;
    }
    
    if a[0] == x {
      assert 0 in full_indices;
      assert full_indices == {0} + shifted_indices;
      assert 0 !in shifted_indices;
      assert |full_indices| == 1 + |shifted_indices|;
      assert |full_indices| == 1 + |tail_indices|;
    } else {
      assert 0 !in full_indices;
      assert full_indices == shifted_indices;
      assert |full_indices| == |tail_indices|;
    }
  }
}

lemma count_rec_step(a: seq<int>, x: int, i: int)
  requires 1 <= i <= |a|
  ensures count_rec(a[..i], x) == count_rec(a[..i-1], x) + (if a[i-1] == x then 1 else 0)
{
  var prefix := a[..i-1];
  var full := a[..i];
  assert full == prefix + [a[i-1]];
  
  calc {
    count_rec(full, x);
    count_rec(prefix + [a[i-1]], x);
    {
      if |prefix| == 0 {
        assert prefix == [];
        assert full == [a[i-1]];
      }
    }
    count_rec(prefix, x) + (if a[i-1] == x then 1 else 0);
  }
}

lemma count_step_invariant(a: seq<int>, x: int, i: int, cnt: int)
  requires 0 <= i < |a|
  requires cnt == |set j | 0 <= j < i && a[j] == x|
  ensures cnt + (if a[i] == x then 1 else 0) == |set j | 0 <= j < i + 1 && a[j] == x|
{
  var old_set := set j | 0 <= j < i && a[j] == x;
  var new_set := set j | 0 <= j < i + 1 && a[j] == x;
  
  if a[i] == x {
    assert i in new_set;
    assert i !in old_set;
    assert new_set == old_set + {i};
    assert |new_set| == |old_set| + 1;
    assert |new_set| == cnt + 1;
  } else {
    assert i !in new_set;
    assert new_set == old_set;
    assert |new_set| == cnt;
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
  cnt := 0;
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant cnt == |set j | 0 <= j < i && a[j] == x|
    invariant cnt == count_rec(a[..i], x)
  {
    count_step_invariant(a, x, i, cnt);
    
    if a[i] == x {
      cnt := cnt + 1;
    }
    i := i + 1;
    
    count_rec_step(a, x, i);
  }
  
  assert a[..i] == a;
  count_rec_properties(a, x);
}
// </vc-code>

