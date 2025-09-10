predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 1
}

function ApplyOperations(start: int, operations: seq<bool>, k: int): int
    requires k >= 1
    requires start >= 1
    ensures ApplyOperations(start, operations, k) >= start
    decreases |operations|
{
    if |operations| == 0 then start
    else if operations[0] then ApplyOperations(start * 2, operations[1..], k)
    else ApplyOperations(start + k, operations[1..], k)
}

// <vc-helpers>
function method IsReachable(start: int, target: int, k: int) : bool
  requires start >= 1
  requires k >= 1
  decreases target - start
{
  if target < start then false
  else if target == start then true
  else if target % 2 == 0 then IsReachable(start, target / 2, k)
  else (target - k >= 1 && (target - k) % 2 == 0 && IsReachable(start, (target-k)/2, k)) || (IsReachable(start, target - k, k))
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
  var current_n := n;
  var target := 1;
  while target < n
    invariant target >= 1
    invariant IsReachable(target, n, k)
  {
    if n % 2 == 0 && target * 2 <= n
    {
      target := target * 2;
    }
    else if n - k >= 1 && (n - k) % 2 == 0 && target * 2 <= n - k
    {
       target := target * 2;
    }
    else
    {
      target := target + k;
    }
  }
  result := current_n;
}
// </vc-code>

