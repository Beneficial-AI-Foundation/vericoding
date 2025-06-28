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
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}

}