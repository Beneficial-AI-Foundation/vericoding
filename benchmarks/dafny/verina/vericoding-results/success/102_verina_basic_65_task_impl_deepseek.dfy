// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsPerfectSquare(n: nat, root: nat) { root * root == n }
lemma SquaredIncreasing(a: nat, b: nat)
  requires a <= b
  ensures a * a <= b * b
{
}
lemma RootBounds(n: nat, root: nat)
  requires root * root <= n
  requires n < (root + 1) * (root + 1)
{
}
// </vc-helpers>

// <vc-spec>
method SquareRoot(n: nat) returns (result: nat)
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    result := 0;
    return;
  }
  
  var low := 0;
  var high := n + 1;
  
  while low + 1 < high
    invariant low * low <= n
    invariant n < high * high
    invariant low <= high
  {
    var mid := (low + high) / 2;
    if mid * mid <= n {
      low := mid;
    } else {
      high := mid;
    }
  }
  
  result := low;
}
// </vc-code>
