// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mroot3(n:int) returns (r:int) 
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  var y:int;
  var h:int;
  r:=0;
  y:=n+1;
  while (y!=r+1) 
    invariant r>=0 && r*r<=n<y*y && y>=r+1
    decreases y-r
  {
    h:=(r+y)/2;
    if (h*h<=n)
      {r:=h;}
    else
      {y:=h;} 
  }
}
// </vc-code>
