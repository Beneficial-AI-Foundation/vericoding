function calcSum(n: nat) : nat 
{   
    n * (n - 1) / 2
}

// <vc-helpers>
// </vc-helpers>

method sum(n: nat) returns(s: nat)
    ensures s == calcSum(n + 1)
// </vc-spec>
// <vc-code>
{
    s := 0;
    var i := 0;
    
    while i <= n
        invariant 0 <= i <= n + 1
        invariant s == i * (i - 1) / 2
    {
        s := s + i;
        i := i + 1;
    }
}
// </vc-code>