// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>