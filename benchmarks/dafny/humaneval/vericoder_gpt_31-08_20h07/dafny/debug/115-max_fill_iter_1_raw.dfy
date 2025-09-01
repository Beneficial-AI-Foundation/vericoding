```vc-helpers
lemma SumNonNegInt(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i]
  ensures 0 <= sum(s)
{
  if |s| == 0 {
  } else {
    assert 0 <= s[0];
    assert forall i :: 0 <= i < |s[1..]| ==> 0 <= s[1..][i] by {
      assume 0 <= i < |s[1..]|;
      assert 0 <= i + 1 < |s|;
      assert s[1..][i] == s[i + 1];
    }
    SumNonNegInt(s[1..]);
    assert 0 <= sum(s[1..]);
    assert 0 <= s[0] + sum(s[1..]);
  }
}

lemma SumNatNonNeg(r: seq<nat>)
  ensures 0 <= sum(r)
{
  if |r| == 0 {
  } else {
    SumNatNonNeg(r[1..]);
    assert 0 <= r[0];
    assert 0 <= sum(r[1..]);
    assert 0 <= r[0] + sum(r[1..]);
  }
}

lemma GenSeqElemsNonNeg(grid: seq<seq<nat>>, capacity: nat, len: nat)
  requires capacity > 0
  requires len <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures forall j :: 0 <= j < len ==> 0 <= gen_seq(grid, capacity, len)[j]
{
  assert forall j :: 0 <= j < len ==> 0 <= gen_seq(grid, capacity, len)[j] by {
    assume 0 <= j < len;
    assert j < |grid|;
    SumNatNonNeg(grid[j]);
    assert 0 <= sum(grid[j]);
    assert 0 < capacity;
    assert 0 <= capacity - 1;
    assert 0 <= sum(grid[j]) + capacity - 1;
    assert 0 <= (sum(grid[j]) + capacity - 1) / capacity;
  }
}
```

```vc-code
{
  var s := sum(gen_seq(grid, capacity, |grid|));
  GenSeqElemsNonNeg(grid, capacity, |grid|);
  SumNonNegInt(gen_seq(grid, capacity, |grid|));
  assert s >= 0;
  cnt := s as nat;
}
```