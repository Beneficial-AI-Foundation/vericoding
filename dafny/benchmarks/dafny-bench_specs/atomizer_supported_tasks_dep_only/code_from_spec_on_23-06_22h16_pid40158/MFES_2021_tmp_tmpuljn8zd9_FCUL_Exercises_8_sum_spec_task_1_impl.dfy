// ATOM 
function calcSum(n: nat) : nat 
{   
    n * (n - 1) / 2
}

//IMPL sum
method sum(n: nat) returns(s: nat)
    ensures s == calcSum(n + 1)
{
    s := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant s == calcSum(i + 1)
    {
        i := i + 1;
        s := s + i;
    }
}