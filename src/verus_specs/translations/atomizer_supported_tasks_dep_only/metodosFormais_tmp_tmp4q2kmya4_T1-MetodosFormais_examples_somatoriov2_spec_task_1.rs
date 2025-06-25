use vstd::prelude::*;

spec fn somaAteAberto(a: &[nat], i: nat) -> nat
    recommends i <= a.len()
{
    if i == 0 {
        0
    } else {
        a[i-1] + somaAteAberto(a, i-1)
    }
}

pub fn somatorio(a: &[nat]) -> (s: nat)
    ensures s == somaAteAberto(a, a.len())
{
}