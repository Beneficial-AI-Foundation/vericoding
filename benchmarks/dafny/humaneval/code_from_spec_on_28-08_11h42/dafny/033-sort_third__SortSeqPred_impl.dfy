method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreservationLemma<T>(s: seq<T>, t: seq<T>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s| && i != j
  requires |s| == |t|
  requires t == s[i := s[j]][j := s[i]]
  ensures multiset(s) == multiset(t)
{
  var temp := s[i := s[j]];
  assert t == temp[j := s[i]];
  assert multiset(s) == multiset(t);
}

lemma SortedPreservationLemma(s: seq<int>, p: seq<bool>, i: int, j: int)
  requires |s| == |p|
  requires 0 <= i < j < |s|
  requires p[i] && p[j]
  requires s[i] > s[j]
  requires forall k, l :: 0 <= k < l < |s| && p[k] && p[l] && (k != i || l != j) ==> s[k] <= s[l]
  ensures forall k, l :: 0 <= k < l < |s| && p[k] && p[l] ==> (s[i := s[j]][j := s[i]])[k] <= (s[i := s[j]][j := s[i]])[l]
{
  var swapped := s[i := s[j]][j := s[i]];
  forall k, l | 0 <= k < l < |s| && p[k] && p[l]
    ensures swapped[k] <= swapped[l]
  {
    if k == i && l == j {
      assert swapped[k] == s[j] && swapped[l] == s[i];
      assert s[i] > s[j];
      assert swapped[k] <= swapped[l];
    } else if k == i && l != j {
      assert swapped[k] == s[j];
      if l == i {
        assert swapped[l] == s[j];
      } else {
        assert swapped[l] == s[l];
      }
    } else if k != i && l == j {
      if k == j {
        assert swapped[k] == s[i];
      } else {
        assert swapped[k] == s[k];
      }
      assert swapped[l] == s[i];
    } else {
      if k == j {
        assert swapped[k] == s[i];
      } else {
        assert swapped[k] == s[k];
      }
      if l == i {
        assert swapped[l] == s[j];
      } else {
        assert swapped[l] == s[l];
      }
      if k != j && l != i {
        assert s[k] <= s[l];
      }
    }
  }
}

predicate IsSorted(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
{
  forall i, j :: 0 <= i < j < |s| && p[i] && p[j] ==> s[i] <= s[j]
}

predicate Unchanged(s: seq<int>, t: seq<int>, p: seq<bool>)
  requires |s| == |t| == |p|
{
  forall i :: 0 <= i < |s| && !p[i] ==> s[i] == t[i]
}

lemma SwapPreservesUnchanged(s: seq<int>, p: seq<bool>, i: int, j: int)
  requires |s| == |p|
  requires 0 <= i < j < |s|
  requires p[i] && p[j]
  ensures Unchanged(s, s[i := s[j]][j := s[i]], p)
{
  var swapped := s[i := s[j]][j := s[i]];
  forall k | 0 <= k < |s| && !p[k]
    ensures swapped[k] == s[k]
  {
    if k == i {
      assert false;
    } else if k == j {
      assert false;
    } else {
      assert swapped[k] == s[k];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := s;
  
  var n := |s|;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant Unchanged(s, sorted, p)
    invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> sorted[k] <= sorted[l]
    invariant forall k, l :: 0 <= k < i && i <= l < |sorted| && p[k] && p[l] ==> sorted[k] <= sorted[l]
  {
    if p[i] {
      var j := i + 1;
      while j < n
        invariant i < j <= n
        invariant |sorted| == |s|
        invariant multiset(s) == multiset(sorted)
        invariant Unchanged(s, sorted, p)
        invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> sorted[k] <= sorted[l]
        invariant forall k, l :: 0 <= k < i && i <= l < |sorted| && p[k] && p[l] ==> sorted[k] <= sorted[l]
        invariant forall l :: i < l < j && p[l] ==> sorted[i] <= sorted[l]
      {
        if p[j] && sorted[i] > sorted[j] {
          SwapPreservesUnchanged(sorted, p, i, j);
          MultisetPreservationLemma(sorted, sorted[i := sorted[j]][j := sorted[i]], i, j);
          var old_sorted := sorted;
          sorted := sorted[i := sorted[j]][j := sorted[i]];
          
          forall k, l | 0 <= k < l < i && p[k] && p[l]
            ensures sorted[k] <= sorted[l]
          {
            assert old_sorted[k] <= old_sorted[l];
            if k == i {
              assert sorted[k] == old_sorted[j];
            } else if k == j {
              assert sorted[k] == old_sorted[i];
            } else {
              assert sorted[k] == old_sorted[k];
            }
            if l == i {
              assert sorted[l] == old_sorted[j];
            } else if l == j {
              assert sorted[l] == old_sorted[i];
            } else {
              assert sorted[l] == old_sorted[l];
            }
          }
          
          forall k, l | 0 <= k < i && i <= l < |sorted| && p[k] && p[l]
            ensures sorted[k] <= sorted[l]
          {
            if l == i {
              assert sorted[l] == old_sorted[j];
              assert old_sorted[k] <= old_sorted[i];
              assert old_sorted[i] > old_sorted[j];
              if k == i {
                assert sorted[k] == old_sorted[j];
              } else if k == j {
                assert sorted[k] == old_sorted[i];
              } else {
                assert sorted[k] == old_sorted[k];
              }
            } else if l == j {
              assert sorted[l] == old_sorted[i];
              assert old_sorted[k] <= old_sorted[i];
              if k == i {
                assert sorted[k] == old_sorted[j];
              } else if k == j {
                assert sorted[k] == old_sorted[i];
              } else {
                assert sorted[k] == old_sorted[k];
              }
            } else {
              if k == i {
                assert sorted[k] == old_sorted[j];
              } else if k == j {
                assert sorted[k] == old_sorted[i];
              } else {
                assert sorted[k] == old_sorted[k];
              }
              if l == i {
                assert sorted[l] == old_sorted[j];
              } else if l == j {
                assert sorted[l] == old_sorted[i];
              } else {
                assert sorted[l] == old_sorted[l];
              }
              assert old_sorted[k] <= old_sorted[l];
            }
          }
          
          forall l | i < l < j && p[l]
            ensures sorted[i] <= sorted[l]
          {
            assert sorted[i] == old_sorted[j];
            assert old_sorted[i] <= old_sorted[l];
            assert old_sorted[i] > old_sorted[j];
            if l == i {
              assert sorted[l] == old_sorted[j];
            } else if l == j {
              assert sorted[l] == old_sorted[i];
            } else {
              assert sorted[l] == old_sorted[l];
            }
            assert sorted[i] <= sorted[l];
          }
        }
        j := j + 1;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
