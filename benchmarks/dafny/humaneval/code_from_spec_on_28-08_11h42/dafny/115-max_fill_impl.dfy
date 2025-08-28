// <vc-helpers>
lemma SumNonNegative(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures sum(s) >= 0
{
  if |s| == 0 {
  } else {
    SumNonNegative(s[1..]);
  }
}

lemma SumAdditive(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    SumAdditive(s1[1..], s2);
    calc {
      sum(s1 + s2);
      == (s1 + s2)[0] + sum((s1 + s2)[1..]);
      == s1[0] + sum(s1[1..] + s2);
      == s1[0] + sum(s1[1..]) + sum(s2);
      == sum(s1) + sum(s2);
    }
  }
}

lemma SumSeqNat(s: seq<nat>)
  ensures sum(s) >= 0
{
  SumNonNegative(s);
}

lemma DivisionProperty(a: nat, b: nat)
  requires b > 0
  ensures (a + b - 1) / b >= 0
{
}

lemma SumSliceProperty(s: seq<nat>, j: nat)
  requires j <= |s|
  ensures sum(s[..j]) >= 0
{
  SumNonNegative(s[..j]);
}

lemma SumSliceExtend(s: seq<nat>, j: nat)
  requires j < |s|
  ensures sum(s[..j+1]) == sum(s[..j]) + s[j]
{
  if j == 0 {
    assert s[..j] == [];
    assert s[..j+1] == [s[0]];
  } else {
    assert s[..j+1] == s[..j] + [s[j]];
    SumAdditive(s[..j], [s[j]]);
  }
}

lemma GenSeqProperties(grid: seq<seq<nat>>, capacity: nat, i: nat)
  requires capacity > 0
  requires i < |grid|
  requires forall k, j :: 0 <= k < |grid| && 0 <= j < |grid[k]| ==> grid[k][j] == 0 || grid[k][j] == 1
  ensures gen_seq(grid, capacity, i + 1) == gen_seq(grid, capacity, i) + [(sum(grid[i]) + capacity - 1) / capacity]
{
  var left := gen_seq(grid, capacity, i);
  var right := [(sum(grid[i]) + capacity - 1) / capacity];
  var combined := gen_seq(grid, capacity, i + 1);
  
  assert |left| == i;
  assert |right| == 1;
  assert |combined| == i + 1;
  
  forall k | 0 <= k < i
    ensures combined[k] == left[k]
  {
  }
  
  assert combined[i] == (sum(grid[i]) + capacity - 1) / capacity;
  assert combined == left + right;
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
  cnt := 0;
  var i := 0;
  
  while i < |grid|
    invariant 0 <= i <= |grid|
    invariant cnt == sum(gen_seq(grid, capacity, i))
    invariant cnt >= 0
  {
    var row_sum := 0;
    var j := 0;
    
    while j < |grid[i]|
      invariant 0 <= j <= |grid[i]|
      invariant row_sum == sum(grid[i][..j])
      invariant row_sum >= 0
    {
      SumSliceExtend(grid[i], j);
      row_sum := row_sum + grid[i][j];
      j := j + 1;
    }
    
    assert grid[i][..|grid[i]|] == grid[i];
    assert row_sum == sum(grid[i]);
    
    var buckets := (row_sum + capacity - 1) / capacity;
    DivisionProperty(row_sum, capacity);
    
    GenSeqProperties(grid, capacity, i);
    assert gen_seq(grid, capacity, i + 1) == gen_seq(grid, capacity, i) + [buckets];
    
    SumAdditive(gen_seq(grid, capacity, i), [buckets]);
    assert sum(gen_seq(grid, capacity, i + 1)) == sum(gen_seq(grid, capacity, i)) + buckets;
    assert sum(gen_seq(grid, capacity, i)) == cnt;
    assert buckets >= 0;
    
    cnt := cnt + buckets;
    
    i := i + 1;
  }
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