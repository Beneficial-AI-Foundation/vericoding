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
            // Help Verus understand the recursive definition
            assert(i + 1 <= a.len());
            assert((i + 1) as nat <= a.len());
            assert(somaAteAberto(a, (i + 1) as nat) == 
                   somaAteAberto(a, i as nat) + a[i as int]);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}

}