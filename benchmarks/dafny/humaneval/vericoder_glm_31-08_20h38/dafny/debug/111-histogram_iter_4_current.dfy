type BiggestMap = map<int, int>

// <vc-helpers>
function {:opaque} count_occurrences(a: seq<int>, i: int): int
  reads nothing
  ensures count_occurrences(a, i) == |set j | 0 <= j < |a| && a[j] == i|
{
  if |a| == 0 then 0 else
  if a[0] == i then
    1 + count_occurrences(a[1..], i)
  else
    count_occurrences(a[1..], i)
}

lemma count_occurrences_property(a: seq<int>, i: int)
  ensures count_occurrences(a, i) == |set j | 0 <= j < |a| && a[j] == i|
{
  reveal count_occurrences();
  if |a| == 0 {
    calc {
      |set j | 0 <= j < |a| && a[j] == i|;
      |set j | 0 <= j < 0 && a[j] == i|;
      |{}|;
      0;
    }
  } else if a[0] == i {
    calc {
      |set j | 0 <= j < |a| && a[j] == i|;
      |set j | (0 <= j < |a| && a[j] == i && j == 0) || (0 <= j < |a| && a[j] == i && j != 0)|;
      |set j | j == 0| + |set j | 0 < j < |a| && a[j] == a[0]|;
      1 + |set k | 0 <= k < |a[1..]| && a[1..][k] == a[0]|;
      {
        count_occurrences_property(a[1..], i);
      }
      1 + count_occurrences(a[1..], i);
    }
  } else {
    calc {
      |set j | 0 <= j < |a| && a[j] == i|;
      |set j | 0 < j < |a| && a[j] == i|;
      |set k | 0 <= k < |a[1..]| && a[1..][k] == i|;
      {
        count_occurrences_property(a[1..], i);
      }
      count_occurrences(a[1..], i);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>) returns (biggest: BiggestMap)
  // post-conditions-start
  ensures forall i :: 0 <= i < |a| && a[i] in biggest ==>
    biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==>
    biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==>
    biggest[a[i]] == biggest[a[j]]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var m := map[];
  var maxCount := 0;
  
  for i := 0 to |a|
  invariant forall k :: k in m ==> m[k] == count_occurrences(a, k)
  invariant forall k :: k in m ==> count_occurrences(a, k) == maxCount
  {
    if i < |a| && a[i] !in m {
      var count := count_occurrences(a, a[i]);
      count_occurrences_property(a, a[i]);
      if count > maxCount {
        maxCount := count;
        m := map[a[i] := count];
      } else if count == maxCount {
        m := m[a[i] := count];
      } else {
        assert count < maxCount;
      }
    }
  }
  
  biggest := m;
  
  forall i | 0 <= i < |a| && a[i] in m
    ensures m[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  {
    count_occurrences_property(a, a[i]);
  }
  
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && a[i] in m
    ensures m[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  {
    calc {
      m[a[i]];
      maxCount;
      >= count_occurrences(a, a[j]);
      {
        count_occurrences_property(a, a[j]);
      }
      |set k | 0 <= k < |a| && a[k] == a[j]|;
    }
  }
  
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && a[i] in m && a[j] in m
    ensures m[a[i]] == m[a[j]]
  {
    assert m[a[i]] == maxCount;
    assert m[a[j]] == maxCount;
  }
}
// </vc-code>

