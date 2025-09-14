// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SquareRoot(n: nat) returns (result: nat)
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
  var r := 0;
  while (r+1)*(r+1) <= n
      invariant r * r <= n
      invariant r <= n
  {
    r := r + 1;
  }
  result := r;
}
// </vc-code>
