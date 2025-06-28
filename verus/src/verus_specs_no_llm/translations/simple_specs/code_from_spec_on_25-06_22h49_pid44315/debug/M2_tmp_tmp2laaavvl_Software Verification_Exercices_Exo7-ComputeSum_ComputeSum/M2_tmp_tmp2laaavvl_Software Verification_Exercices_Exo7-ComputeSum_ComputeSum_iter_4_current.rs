use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + Sum((n - 1) as nat) }
}

fn ComputeSum(n: nat) -> (s: nat)
    ensures
        s == Sum(n)
{
    let mut i: nat = 0;
    let mut sum: nat = 0;
    
    while i < n
        invariant 
            i <= n,
            sum == Sum(i)
        decreases n - i
    {
        i = i + 1;
        sum = sum + i;
        
        // Proof hint: after incrementing i and adding i to sum,
        // sum should equal Sum(i) because Sum(i) = i + Sum(i-1)
        // and we had sum == Sum(i-1) before the iteration
        assert(sum == Sum(i)) by {
            // The recursive definition of Sum gives us:
            // Sum(i) = i + Sum(i-1)
            // We had sum == Sum(i-1) before adding i
            // So sum + i == Sum(i-1) + i == Sum(i)
        }
    }
    
    sum
}

}