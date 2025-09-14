

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  r := 0;
  while (r + 1) * (r + 1) <= n
    invariant r >= 0
    invariant r * r <= n
  {
    r := r + 1;
  }
}
// </vc-code>

