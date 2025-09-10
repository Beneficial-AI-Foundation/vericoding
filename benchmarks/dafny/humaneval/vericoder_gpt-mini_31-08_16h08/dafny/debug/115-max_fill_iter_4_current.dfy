

// <vc-helpers>
lemma SumCons(x: int, s: seq<int>)
  ensures sum([x] + s) == x + sum(s)
{
  if |s| == 0 {
    assert [x] + s == [x];
    assert sum([x]) == x + 0;
  } else {
    // By definition of sequence indexing and sum
    assert ([x] + s)[0] == x;
    assert ([x] + s)[1..] == s;
    assert sum([x] + s) == x + sum(s);
  }
}

lemma SumNonneg(s: seq<nat>)
  ensures sum(s) >= 0
  decreases |s|
{
  if |s| == 0 {
    assert sum(s) == 0;
  } else {
    var x := s[0];
    var rest := s[1..];
    SumNonneg(rest);
    // sum(s) == x + sum(rest) and both terms non-negative
    assert sum(s) == x + sum(rest);
    assert x >= 0;
    assert sum(rest) >= 0;
    assert sum(s) >= 0;
  }
}

lemma SumConcat(a: seq<int>, b: seq<int>)
  ensures sum(a + b) == sum(a) + sum(b)
  decreases |a|
{
  if |a| == 0 {
    assert a == [];
    assert a + b == b;
    assert sum(a + b) == sum(b);
    assert sum(a) == 0;
    assert sum(a + b) == sum(a) + sum(b);
  } else {
    var x := a[0];
    var rest := a[1..];
    assert a == [x] + rest;
    assert a + b == [x] + (rest + b);
    // sum([x] + s) == x + sum(s)
    SumCons(x, rest + b);
    assert sum(a + b) == x + sum(rest + b);
    SumConcat(rest, b);
    assert sum(rest + b) == sum(rest) + sum(b);
    assert sum(a) == x + sum(rest);
    assert sum(a + b) == sum(a) + sum(b);
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
  var i := 0;
  var acc: int := 0;
  while i < |grid|
    invariant 0 <= i <= |grid|
    invariant acc == sum(gen_seq(grid, capacity, i))
    invariant acc >= 0
  {
    var s := sum(grid[i]);
    // prove s >= 0
    SumNonneg(grid[i]);
    assert s >= 0;
    var need := (s + capacity - 1) / capacity;
    // relate gen_seq for i and i+1
    GenSeqAppend(grid, capacity, i);
    // sum(gen_seq(..., i+1)) == sum(gen_seq(..., i)) + need
    SumConcat(gen_seq(grid, capacity, i), [need]);
    assert sum(gen_seq(grid, capacity, i + 1)) == sum(gen_seq(grid, capacity, i)) + need;
    // prove need >= 0 (using division properties)
    assert s + capacity - 1 >= 0;
    assert (s + capacity - 1) == capacity * need + (s + capacity - 1) % capacity;
    assert 0 <= (s + capacity - 1) % capacity;
    assert capacity * need >= 0;
    assert need >= 0;
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