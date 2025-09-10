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
function CanCover(tasks: seq<int>, n: int, m: int, t: int): bool
  requires ValidInput(n, m, tasks)
{
  var i: int := 0;
  var count: int := 0;
  while i < |tasks|
    invariant ValidInput(n, m, tasks)
    invariant 0 <= i <= |tasks|
    invariant 0 <= count <= m
  {
    var start := tasks[i];
    var j := i;
    while j < |tasks| && ((tasks[j] - start + n) % n) <= t
      invariant ValidInput(n, m, tasks)
      invariant i <= j <= |tasks|
      invariant forall k :: i <= k < j ==> ((tasks[k] - start + n) % n) <= t
    {
      j := j + 1;
    }
    if j == i {
      return false;
    }
    count := count + 1;
    i := j;
    if count > m {
      return false;
    }
  }
  return count <= m;
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
  var low: int := 0;
  var high: int := n - 1;
  while low < high
    invariant 0 <= low <= high <= n - 1
    invariant exists t :: low <= t <= high && CanCover(tasks, n, m, t)
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    if CanCover(tasks, n, m, mid) {
      high := mid;
    } else {
      low := mid + 1;
    }
  }
  result := low;
}
// </vc-code>

