use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SomaAte(a: Seq<nat>, n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n <= a.len() {
        SomaAte(a, n - 1) + a[(n - 1) as int]
    } else {
        SomaAte(a, a.len())
    }
}

// Helper lemma to prove properties about SomaAte
proof fn lemma_soma_ate_extend(a: Seq<nat>, n: nat)
    requires n < a.len()
    ensures SomaAte(a, n + 1) == SomaAte(a, n) + a[n as int]
    decreases n + 1
{
    if n == 0 {
        assert(SomaAte(a, 1) == SomaAte(a, 0) + a[0]);
    } else {
        lemma_soma_ate_extend(a, n - 1);
    }
}

fn Somatorio(a: Vec<nat>) -> (s: nat)
    ensures
        s == SomaAte(a@, a.len() as nat)
{
    let mut sum: nat = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum == SomaAte(a@, i as nat),
    {
        proof {
            if i < a.len() {
                lemma_soma_ate_extend(a@, i as nat);
            }
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}

}