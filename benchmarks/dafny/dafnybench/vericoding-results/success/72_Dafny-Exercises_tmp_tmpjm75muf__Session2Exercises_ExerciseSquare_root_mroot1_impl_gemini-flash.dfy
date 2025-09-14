

// <vc-helpers>
function Square(x:int): int {
    x*x
}
// </vc-helpers>

// <vc-spec>
method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
    r := 0;
    while Square(r + 1) <= n
        invariant r >= 0
        invariant Square(r) <= n
        decreases n - Square(r)
    {
        r := r + 1;
    }
}
// </vc-code>

