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
  result := 0;
  while (result + 1) * (result + 1) <= n
    invariant result * result <= n
  {
    result := result + 1;
  }
}
// </vc-code>
