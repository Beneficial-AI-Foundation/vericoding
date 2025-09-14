

// <vc-helpers>
lemma SqrtLemma(n: nat, r: nat)
  requires r*r <= n < (r+1)*(r+1)
  ensures n == 0 ==> r == 0
  ensures n > 0 ==> r*r <= n < (r+1)*(r+1)
{
}

predicate IsPerfectSquare(n: nat)
  decreases n
{
  if n == 0 then true
  else exists r: nat | 0 <= r <= n :: r*r == n
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  if N == 0 {
    return 0;
  }
  
  var current := 0;
  while (current + 1) * (current + 1) <= N
    invariant current * current <= N
    decreases N - current
  {
    current := current + 1;
  }
  
  return current;
}
// </vc-code>

