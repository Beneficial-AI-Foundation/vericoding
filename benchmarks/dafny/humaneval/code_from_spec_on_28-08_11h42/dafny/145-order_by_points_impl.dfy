function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
lemma digits_sum_deterministic(x: int, y: int)
  ensures x == y ==> digits_sum(x) == digits_sum(y)
{
}

lemma multiset_insert_permutation<T>(s: seq<T>, x: T, i: int)
  requires 0 <= i <= |s|
  ensures multiset(s + [x]) == multiset(s[..i] + [x] + s[i..])
{
  if i == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
    assert s[..i] + [x] + s[i..] == [] + [x] + s == [x] + s;
  } else if i == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
    assert s[..i] + [x] + s[i..] == s + [x] + [] == s + [x];
  } else {
    assert s == s[..i] + s[i..];
  }
}

lemma multiset_swap<T>(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
  var s1 := s[i := s[j]];
  var s2 := s1[j := s[i]];
  assert multiset(s) == multiset(s2);
}

lemma selection_sort_maintains_order(s: seq<int>, i: int, minIdx: int)
  requires 0 <= i < |s|
  requires i <= minIdx < |s|
  requires forall k :: i <= k < |s| ==> digits_sum(s[minIdx]) <= digits_sum(s[k])
  requires forall x, y :: 0 <= x < y < i ==> digits_sum(s[x]) <= digits_sum(s[y])
  requires forall x :: 0 <= x < i ==> digits_sum(s[x]) <= digits_sum(s[minIdx])
  ensures forall x, y {:trigger digits_sum(s[i := s[minIdx]][minIdx := s[i]][x]), digits_sum(s[i := s[minIdx]][minIdx := s[i]][y])} :: 
    0 <= x < y < i + 1 ==> digits_sum(s[i := s[minIdx]][minIdx := s[i]][x]) <= digits_sum(s[i := s[minIdx]][minIdx := s[i]][y])
{
  var temp := s[i];
  var s_new := s[i := s[minIdx]][minIdx := temp];
  
  forall x, y | 0 <= x < y < i + 1
    ensures digits_sum(s_new[x]) <= digits_sum(s_new[y])
  {
    if y < i {
      if x != i && y != i && x != minIdx && y != minIdx {
        assert s_new[x] == s[x];
        assert s_new[y] == s[y];
      } else if x == i {
        assert false;
      } else if y == i {
        assert false;
      } else if x == minIdx && y != i {
        assert s_new[x] == temp;
        if y == minIdx {
          assert false;
        } else {
          assert s_new[y] == s[y];
        }
      } else if y == minIdx && x != i {
        assert s_new[y] == temp;
        assert s_new[x] == s[x];
      }
    } else {
      assert y == i;
      assert s_new[i] == s[minIdx];
      if x < i {
        if x != minIdx {
          assert s_new[x] == s[x];
        } else {
          assert s_new[minIdx] == temp;
          assert temp == s[i];
        }
      }
    }
  }
}

lemma ordered_prefix_property(s: seq<int>, i: int)
  requires 0 <= i < |s|
  requires forall x, y :: 0 <= x < y < i ==> digits_sum(s[x]) <= digits_sum(s[y])
  requires i > 0 ==> forall k :: i <= k < |s| ==> digits_sum(s[i-1]) <= digits_sum(s[k])
  ensures forall x :: 0 <= x < i ==> digits_sum(s[x]) <= digits_sum(s[i])
{
}

lemma min_element_property(s: seq<int>, i: int, minIdx: int)
  requires 0 <= i < |s| && i <= minIdx < |s|
  requires forall k :: i <= k < |s| ==> digits_sum(s[minIdx]) <= digits_sum(s[k])
  requires forall x :: 0 <= x < i ==> digits_sum(s[x]) <= digits_sum(s[minIdx])
  ensures forall x :: 0 <= x < i ==> digits_sum(s[x]) <= digits_sum(s[minIdx])
{
}

lemma swap_preserves_order(s: seq<int>, i: int, minIdx: int)
  requires 0 <= i < |s| && i <= minIdx < |s|
  requires forall k :: i <= k < |s| ==> digits_sum(s[minIdx]) <= digits_sum(s[k])
  requires forall x, y :: 0 <= x < y < i ==> digits_sum(s[x]) <= digits_sum(s[y])
  requires forall x :: 0 <= x < i ==> digits_sum(s[x]) <= digits_sum(s[minIdx])
  ensures var sorted := s[i := s[minIdx]][minIdx := s[i]];
          forall x, y :: 0 <= x < y < i + 1 ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
{
  var sorted := s[i := s[minIdx]][minIdx := s[i]];
  
  forall x, y | 0 <= x < y < i + 1
    ensures digits_sum(sorted[x]) <= digits_sum(sorted[y])
  {
    if y == i {
      assert sorted[i] == s[minIdx];
      if x < i {
        if x != minIdx {
          assert sorted[x] == s[x];
          assert digits_sum(s[x]) <= digits_sum(s[minIdx]);
          assert digits_sum(sorted[x]) <= digits_sum(sorted[i]);
        } else {
          assert sorted[x] == s[i];
          assert digits_sum(s[i]) >= digits_sum(s[minIdx]);
          assert digits_sum(sorted[x]) <= digits_sum(sorted[i]);
        }
      }
    } else {
      assert y < i;
      if x != minIdx && y != minIdx {
        assert sorted[x] == s[x] && sorted[y] == s[y];
        assert digits_sum(sorted[x]) <= digits_sum(sorted[y]);
      } else if x == minIdx {
        assert sorted[x] == s[i];
        if y == minIdx {
          assert false;
        } else {
          assert sorted[y] == s[y];
          assert y < i;
          assert digits_sum(s[y]) <= digits_sum(s[minIdx]);
          assert digits_sum(s[i]) >= digits_sum(s[minIdx]);
          assert digits_sum(sorted[x]) <= digits_sum(sorted[y]);
        }
      } else if y == minIdx {
        assert sorted[y] == s[i];
        assert sorted[x] == s[x];
        assert x < y < i;
        assert digits_sum(s[x]) <= digits_sum(s[y]);
        assert digits_sum(s[y]) <= digits_sum(s[i]);
        assert digits_sum(sorted[x]) <= digits_sum(sorted[y]);
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := s;
  
  var n := |sorted|;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall x, y :: 0 <= x < y < i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
  {
    var minIdx := i;
    var j := i + 1;
    
    while j < n
      invariant i < j <= n
      invariant i <= minIdx < j
      invariant forall k :: i <= k < j ==> digits_sum(sorted[minIdx]) <= digits_sum(sorted[k])
    {
      if digits_sum(sorted[j]) < digits_sum(sorted[minIdx]) {
        minIdx := j;
      }
      j := j + 1;
    }
    
    if minIdx != i {
      var temp := sorted[i];
      var old_sorted := sorted;
      sorted := sorted[i := sorted[minIdx]][minIdx := temp];
      multiset_swap(old_sorted, i, minIdx);
      
      assert forall k :: i <= k < |old_sorted| ==> digits_sum(old_sorted[minIdx]) <= digits_sum(old_sorted[k]);
      min_element_property(old_sorted, i, minIdx);
      assert forall x :: 0 <= x < i ==> digits_sum(old_sorted[x]) <= digits_sum(old_sorted[minIdx]);
      
      swap_preserves_order(old_sorted, i, minIdx);
      assert forall x, y :: 0 <= x < y < i + 1 ==> digits_sum(sorted[x]) <= digits_sum(sorted[y]);
    } else {
      assert sorted[i] == sorted[minIdx];
      assert forall x, y :: 0 <= x < y < i + 1 ==> digits_sum(sorted[x]) <= digits_sum(sorted[y]);
    }
    
    i := i + 1;
  }
}
// </vc-code>
