use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn soma(a: Vec<nat>, n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n <= a.len() {
        soma(a, (n - 1) as nat) + a[(n - 1) as int]
    } else {
        0
    }
}

fn somatorio(a: Vec<nat>) -> (s: nat)
    ensures
        s == soma(a, a.len())
{
    let mut sum: nat = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum == soma(a, i as nat)
        decreases a.len() - i
    {
        // Prove that i < a.len() implies i + 1 <= a.len()
        assert(i < a.len());
        assert(i + 1 <= a.len());
        
        // Prove the relationship between soma(a, i) and soma(a, i+1)
        assert(i < a.len() ==> soma(a, (i + 1) as nat) == soma(a, i as nat) + a[i as int]);
        
        sum = sum + a[i];
        i = i + 1;
        
        // Help the verifier understand the invariant is maintained
        assert(sum == soma(a, i as nat));
    }
    
    // At this point i == a.len(), so sum == soma(a, a.len())
    assert(i == a.len());
    assert(sum == soma(a, a.len()));
    
    sum
}

}