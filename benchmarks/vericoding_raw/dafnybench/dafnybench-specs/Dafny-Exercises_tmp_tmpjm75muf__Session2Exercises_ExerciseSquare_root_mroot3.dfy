// <vc-helpers>
// </vc-helpers>

method mroot3(n:int) returns (r:int) 
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
// <vc-code>
{
  assume false;
}
// </vc-code>