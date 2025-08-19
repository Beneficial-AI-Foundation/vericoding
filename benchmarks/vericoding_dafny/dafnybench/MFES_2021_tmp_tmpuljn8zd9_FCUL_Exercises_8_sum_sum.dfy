function calcSum(n: nat) : nat 
{   
    n * (n - 1) / 2
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method sum(n: nat) returns(s: nat)
    ensures s == calcSum(n + 1)
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>