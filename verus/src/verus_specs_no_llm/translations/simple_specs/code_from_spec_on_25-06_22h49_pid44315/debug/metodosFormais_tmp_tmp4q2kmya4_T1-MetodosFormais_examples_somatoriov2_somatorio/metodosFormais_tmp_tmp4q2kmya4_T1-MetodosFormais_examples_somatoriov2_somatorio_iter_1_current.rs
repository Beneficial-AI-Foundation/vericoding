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
        somaAteAberto(a, (n - 1) as nat) + a[(n - 1) as int]
    } else {
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
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}

}