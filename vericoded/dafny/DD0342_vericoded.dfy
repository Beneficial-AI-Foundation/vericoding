function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

// <vc-helpers>
lemma RComputation(n: nat)
    ensures R(n) == if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
{
    // This lemma just restates the definition of R for clarity
}
// </vc-helpers>

// <vc-spec>
method calcR(n: nat) returns (r: nat)
    ensures r == R(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    var i := 0;
    r := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant r == R(i)
    {
        i := i + 1;
        if r > i {
            r := r - i;
        } else {
            r := r + i;
        }
    }
}
// </vc-code>

