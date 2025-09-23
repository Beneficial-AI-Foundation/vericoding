// <vc-preamble>
function calcSum(n: nat) : nat 
{   
    n * (n - 1) / 2
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method sum(n: nat) returns(s: nat)
    ensures s == calcSum(n + 1)
// </vc-spec>
// <vc-code>
{
    s := 0;
    var i := 0;
    while i < n 
        decreases n - i
        invariant 0 <= i <= n
        invariant s == calcSum(i + 1)
    {
        i := i + 1;
        s := s + i;
    }
}
// </vc-code>
