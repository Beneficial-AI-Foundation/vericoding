

// <vc-helpers>
lemma SumNonNeg_Seq(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures sum(s) >= 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    assert |s[1..]| == |s| - 1;
    forall i | 0 <= i < |s[1..]| {
      assert i + 1 < |s|;
      assert s[1..][i] == s[i + 1];
      assert s[i + 1] >= 0;
      assert s[1..][i] >= 0;
    }
    SumNonNeg_Seq(s[1..]);
    assert sum(s) == s[0] + sum(s[1..]);
    assert 0 < |s|;
    assert s[0] >= 0;
    assert sum(s[1..]) >= 0;
    assert sum(s) >= 0;
  }
}

lemma GenSeqElemsNonNeg(grid: seq<seq<nat>>, capacity: nat, len: nat)
  requires capacity > 0
  requires len <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures forall j :: 0 <= j < len ==> 0 <= gen_seq(grid, capacity, len)[j]
{
  forall j | 0 <= j < len {
    assert j < |grid|;
    forall k | 0 <= k < |grid[j]| {
      assert grid[j][k] == 0 || grid[j][k] == 1;
      assert grid[j][k] >= 0;
    }
    SumNonNeg_Seq(grid[j]);
    assert sum(grid[j]) >= 0;
    assert capacity - 1 >= 0;
    assert 0 <= sum(grid[j]) + capacity - 1;
    assert gen_seq(grid, capacity, len)[j] == (sum(grid[j]) + capacity - 1) / capacity;
    assert 0 <= gen_seq(grid, capacity, len)[j];
  }
}
// </vc-helpers>

// <vc-spec>
method max_fill(grid: seq<seq<nat>>, capacity: nat) returns (cnt: nat)
  // pre-conditions-start
  requires capacity > 0
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  // pre-conditions-end
  // post-conditions-start
  ensures cnt == sum(gen_seq(grid, capacity, |grid|))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  GenSeqElemsNonNeg(grid, capacity, |grid|);
  SumNonNeg_Seq(gen_seq(grid, capacity, |grid|));
  cnt := sum(gen_seq(grid, capacity, |grid|));
}
// </vc-code>

function gen_seq(grid: seq<seq<nat>>, capacity: nat, len: nat): seq<int>
  requires capacity > 0
  requires len <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
{
  seq(len, j requires 0 <= j < len => (sum(grid[j]) + capacity - 1) / capacity)
}
// pure-end
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end