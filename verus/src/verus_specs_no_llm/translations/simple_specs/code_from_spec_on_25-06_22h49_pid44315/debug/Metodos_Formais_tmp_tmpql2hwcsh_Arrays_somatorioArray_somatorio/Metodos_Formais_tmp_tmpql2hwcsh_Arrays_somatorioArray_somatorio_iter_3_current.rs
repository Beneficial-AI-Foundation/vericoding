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
    assert(i + 1 <= a.len());
    assert(soma(a, i + 1) == soma(a, i) + a[i as int]);
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
        // Prove the relationship between soma(a, i) and soma(a, i+1)
        proof {
            lemma_soma_step(a, i as nat);
        }
        
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}

}