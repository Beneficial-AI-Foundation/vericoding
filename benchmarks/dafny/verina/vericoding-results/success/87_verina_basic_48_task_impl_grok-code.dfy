// <vc-preamble>
ghost predicate IsPerfectSquare(n: nat)
{
    exists i: nat :: i * i == n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPerfectSquareFn(n: int) returns (result: bool)
    requires n >= 0
    ensures result <==> IsPerfectSquare(n as nat)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added loop invariants to prove that IsPerfectSquare holds iff a root is found in the range. */
{
  var low: int := 0;
  var high: int := n;
  while low <= high
    decreases high - low
    invariant 0 <= low <= high + 1 <= n + 1
    invariant forall i: nat :: i < low ==> i * i < n
    invariant forall i: nat :: i > high ==> i * i > n
  {
    var mid := low + (high - low) / 2;
    if mid * mid < n {
      low := mid + 1;
    } else if mid * mid == n {
      result := true;
      return;
    } else {
      high := mid - 1;
    }
  }
  result := false;
}
// </vc-code>
