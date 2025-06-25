// ATOM 
spec fn SomaAte(a: &[nat], i: nat) -> nat
    recommends 0 <= i <= a.len()
{
    if i == 0 {
        0
    } else {
        a[i-1] + SomaAte(a, i-1)
    }
}

// SPEC 
pub fn Somatorio(a: &[nat]) -> (s: nat)
    ensures(s == SomaAte(a, a.len()))
{
}