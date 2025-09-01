

// <vc-helpers>
lemma SumConcat(a: seq<int>, b: seq<int>)
  ensures sum(a + b) == sum(a) + sum(b)
{
  if |a| == 0 {
    // sum([] + b) == sum(b) == 0 + sum(b)
  } else {
    var x := a[0];
    var as := a[1..];
    SumConcat(as, b);
    // sum(a + b) == x + sum(as + b)
    assert sum(a + b) == x + sum(as + b);
    assert sum(as + b) == sum(as) + sum(b);
    assert sum(a) == x + sum(as);
    // therefore sum(a + b) == sum(a) + sum(b)
  }
}

lemma GenSeqAppend(grid: seq<seq<nat>>, capacity: nat, len: nat)
  requires capacity > 0
  requires len + 1 <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures gen_seq(grid, capacity, len + 1) == gen_seq(grid, capacity, len) + [ (sum(grid[len]) + capacity - 1) / capacity ]
{
  // For indices k < len the elements are the same
  forall k | 0 <= k < len
    ensures gen_seq(grid, capacity, len + 1)[k] == gen_seq(grid, capacity, len)[k]
  {
    // By definition of gen_seq comprehension
    assert gen_seq(grid, capacity, len + 1)[k] == (sum(grid[k]) + capacity - 1) / capacity;
    assert gen_seq(grid, capacity, len)[k] == (sum(grid[k]) + capacity - 1) / capacity;
  }
  // Last element of the longer sequence equals the intended value
  assert gen_seq(grid, capacity, len + 1)[len] == (sum(grid[len]) + capacity - 1) / capacity;
  // Lengths match concatenation result
  assert |gen_seq(grid, capacity, len)| == len;
  assert |gen_seq(grid, capacity, len + 1)| == len + 1;
  // Hence the seq equality holds
  assert gen_seq(grid, capacity, len + 1) == gen_seq(grid, capacity, len) + [ (sum(grid[len]) + capacity - 1) / capacity ];
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
  var i := 0;
  var acc: int := 0;
  while i < |grid|
    invariant 0 <= i <= |grid|
    invariant acc == sum(gen_seq(grid, capacity, i))
    invariant acc >= 0
  {
    var s := sum(grid[i]);
    var need := (s + capacity - 1) / capacity;
    // relate gen_seq for i and i+1
    GenSeqAppend(grid, capacity, i);
    // sum(gen_seq(..., i+1)) == sum(gen_seq(..., i)) + need
    SumConcat(gen_seq(grid, capacity, i), [need]);
    assert sum(gen_seq(grid, capacity, i + 1)) == sum(gen_seq(grid, capacity, i)) + need;
    acc := acc + need;
    i := i + 1;
  }
  cnt := acc;
  assert cnt == sum(gen_seq(grid, capacity, |grid|));
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