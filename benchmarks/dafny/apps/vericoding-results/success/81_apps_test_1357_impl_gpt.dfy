predicate ValidInput(n: int, m: int, tasks: seq<int>)
{
    n >= 2 && m >= 1 && |tasks| == m && 
    forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
}

function MinTimeToComplete(n: int, tasks: seq<int>, currentPos: int, taskIndex: int): int
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= currentPos <= n
    requires 0 <= taskIndex < |tasks|
{
    var target := tasks[taskIndex];
    if target >= currentPos then target - currentPos
    else (n - currentPos) + target
}

// <vc-helpers>
lemma MinTimeBounds(n: int, tasks: seq<int>, currentPos: int, ti: int)
  requires n >= 2
  requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
  requires 1 <= currentPos <= n
  requires 0 <= ti < |tasks|
  ensures MinTimeToComplete(n, tasks, currentPos, ti) >= 0
{
  var t := tasks[ti];
  if t >= currentPos {
    assert MinTimeToComplete(n, tasks, currentPos, ti) == t - currentPos;
    assert t - currentPos >= 0;
  } else {
    assert MinTimeToComplete(n, tasks, currentPos, ti) == (n - currentPos) + t;
    assert n - currentPos >= 0;
    assert t >= 1;
    assert (n - currentPos) + t >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, tasks: seq<int>) returns (result: int)
    requires ValidInput(n, m, tasks)
    ensures result >= 0
    ensures m > 0 ==> result >= tasks[m-1] - 1
    ensures result <= (m - 1) * n + tasks[m-1] - 1
// </vc-spec>
// <vc-code>
{
  var len := |tasks|;
  assert len == m;
  var pos := 1;
  var time := 0;
  var wraps := 0;
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant 1 <= pos <= n
    invariant time >= 0
    invariant wraps >= 0
    invariant pos == (if i == 0 then 1 else tasks[i-1])
    invariant time == (if i == 0 then 0 else tasks[i-1] - 1 + wraps * n)
    invariant wraps <= (if i == 0 then 0 else i - 1)
    decreases len - i
  {
    var target := tasks[i];
    if target >= pos {
      assert target - pos >= 0;
      time := time + (target - pos);
    } else {
      if i == 0 {
        assert pos == 1;
        assert 1 <= target;
        assert target >= pos;
        assert false; // unreachable
      }
      assert n - pos >= 0;
      assert target >= 1;
      time := time + (n - pos) + target;
      wraps := wraps + 1;
    }
    pos := target;
    i := i + 1;
  }
  result := time;

  // Postconditions
  assert m == len;
  assert m >= 1;
  assert result == tasks[m-1] - 1 + wraps * n;
  assert wraps >= 0;
  assert n >= 0;
  assert result >= tasks[m-1] - 1;
  assert wraps <= m - 1;
  assert wraps * n <= (m - 1) * n;
  assert result <= (m - 1) * n + tasks[m-1] - 1;
}
// </vc-code>

