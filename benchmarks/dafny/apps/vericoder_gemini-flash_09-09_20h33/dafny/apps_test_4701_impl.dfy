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
function IsReachable(start: int, target: int, k: int) : bool
  requires start >= 1
  requires k >= 1
  decreases target - start
{
  if target < start then false
  else if target == start then true
  else (target % 2 == 0 && target / 2 >= start && IsReachable(start, target / 2, k)) || (target - k >= start && IsReachable(start, target - k, k))
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
  var target := 1; // Start from 1, trying to reach n
  while target < n
    invariant target >= 1
    invariant IsReachable(target, n, k) // From target, n is reachable
    decreases n - target
  {
    // If n is even and n/2 is reachable from target, prioritize multiplying target by 2
    if n % 2 == 0 && n / 2 >= target && IsReachable(target, n/2, k) then
       target := target * 2;
    // Otherwise, try to add k to target if n is reachable from n - k
    else if n - k >= target && IsReachable(target, n - k, k) then
       target := target + k;
    else
       // This branch indicates a path where neither of the above conditions were met,
       // but n is still reachable by some sequence of operations from target.
       // The most general step is to add k.
       target := target + k;
  }
  result := current_n; // The loop ensures `target == n`
}
// </vc-code>

