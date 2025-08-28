// <vc-helpers>
lemma SquareRootProperty(N: nat, r: nat)
  ensures r*r <= N < (r+1)*(r+1) ==> r == r
{
  // This lemma is trivial as it restates the condition
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
// </vc-spec>
// </vc-spec>

// <vc-code>
method SquareRootImpl(N: nat) returns (r: nat)
  ensures r*r <= N < (r+1)*(r+1)
{
  r := 0;
  while r*r <= N
    invariant r*r <= N
    invariant forall k :: 0 <= k <= r ==> k*k <= N
    decreases N - r*r
  {
    r := r + 1;
  }
  if r > 0 {
    r := r - 1;
  }
}
// </vc-code>
