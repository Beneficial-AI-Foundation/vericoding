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
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}

}