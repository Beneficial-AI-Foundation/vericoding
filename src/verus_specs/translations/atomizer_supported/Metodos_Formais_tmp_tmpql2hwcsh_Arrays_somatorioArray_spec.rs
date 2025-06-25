use vstd::prelude::*;

spec fn soma(a: &[nat], i: nat) -> nat
    recommends i <= a.len()
{
    if i == 0 {
        0
    } else {
        a[i-1] + soma(a, i-1)
    }
}

pub fn somatorio(a: &[nat]) -> (s: nat)
    ensures s == soma(a, a.len())
{
}