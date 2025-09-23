// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
    r:=n;
    while n<r*r
    invariant 0<=r<=n && n<(r+1)*(r+1)//write the invariant
    invariant r*r<=n ==> n<(r+1)*(r+1)
    decreases r//write the bound
    {
        r:=r-1;
    }
}
// </vc-code>
