

// <vc-helpers>
lemma lemma_square_monotonic(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a <= b <==> a*a <= b*b
{
}
// </vc-helpers>

// <vc-spec>
method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  var x := 0;
  while (x + 1) * (x + 1) <= n
    invariant x >= 0
    invariant x * x <= n
  {
    x := x + 1;
  }
  r := x;
}
// </vc-code>

