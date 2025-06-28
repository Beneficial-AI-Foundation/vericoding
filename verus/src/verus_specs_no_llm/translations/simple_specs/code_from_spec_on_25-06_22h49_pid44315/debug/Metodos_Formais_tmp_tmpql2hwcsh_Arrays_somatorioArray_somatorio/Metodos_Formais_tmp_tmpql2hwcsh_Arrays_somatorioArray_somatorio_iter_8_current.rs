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

// Helper lemma to prove the relationship between consecutive soma calls
proof fn lemma_soma_step(a: Vec<nat>, i: nat)
    requires
        i < a.len()
    ensures
        soma(a, i + 1) == soma(a, i) + a[i as int]
{
    // The proof follows from the definition of soma
    assert(i + 1 > 0);
    assert(i + 1 <= a.len());
    assert(i + 1 - 1 == i);
    // By definition of soma, since i + 1 > 0 and i + 1 <= a.len():
    // soma(a, i + 1) expands to soma(a, (i + 1 - 1)) + a[((i + 1) - 1) as int]
    // which is soma(a, i) + a[i as int]
}

// Additional helper lemma for the loop invariant
proof fn lemma_soma_bound(a: Vec<nat>, n: nat)
    requires
        n <= a.len()
    ensures
        soma(a, n) >= 0
{
    // This follows from the fact that all elements are nat (>= 0)
}

fn somatorio(a: Vec<nat>) -> (s: nat)
    ensures
        s == soma(a, a.len() as nat)
{
    let mut sum: nat = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum == soma(a, i as nat)
        decreases a.len() - i
    {
        // Call the lemma before the update
        lemma_soma_step(a, i as nat);
        
        // Update sum and i
        sum = sum + a[i];
        i = i + 1;
        
        // Help verification understand that (i as nat) after increment
        // equals ((i-1) as nat) + 1, which is what we need for the invariant
        assert(i > 0);
        assert((i - 1) as nat + 1 == i as nat);
    }
    
    sum
}

}