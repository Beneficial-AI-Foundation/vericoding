// The specification requires that the returned value `c` equals `n * n * n`. This is a straightforward implementation - I just need to compute the cube and return it.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Cube(n: nat) returns (c: nat) 
    ensures c == n * n * n
// </vc-spec>
// <vc-code>
{
  c := n * n * n;
}
// </vc-code>