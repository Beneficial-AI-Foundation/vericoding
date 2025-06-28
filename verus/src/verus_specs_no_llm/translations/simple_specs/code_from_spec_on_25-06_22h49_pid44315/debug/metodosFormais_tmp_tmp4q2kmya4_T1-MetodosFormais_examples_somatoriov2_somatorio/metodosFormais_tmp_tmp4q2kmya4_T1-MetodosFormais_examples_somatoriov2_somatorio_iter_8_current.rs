use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn somaAteAberto(a: Vec<nat>, n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n <= a.len() {
        somaAteAberto(a, n - 1) + a[(n - 1) as int]
    } else {
        // When n > a.len(), we sum up to a.len()
        somaAteAberto(a, a.len())
    }
}

// Helper lemma to prove properties about somaAteAberto
proof fn lemma_somaAteAberto_step(a: Vec<nat>, i: nat)
    requires
        i < a.len(),
    ensures
        somaAteAberto(a, i + 1) == somaAteAberto(a, i) + a[i as int],
{
    // The proof follows from the definition since i + 1 <= a.len()
}

fn somatorio(a: Vec<nat>) -> (s: nat)
    ensures
        s == somaAteAberto(a, a.len())
{
    let mut sum: nat = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum == somaAteAberto(a, i as nat)
    {
        proof {
            // Prove that we can safely access a[i] and update the sum
            assert(i < a.len());
            assert((i as nat) < a.len());
            lemma_somaAteAberto_step(a, i as nat);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    // At this point, i == a.len(), so sum == somaAteAberto(a, a.len())
    sum
}

}