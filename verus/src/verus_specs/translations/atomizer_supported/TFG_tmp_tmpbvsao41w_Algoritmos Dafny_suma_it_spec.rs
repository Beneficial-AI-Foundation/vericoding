use vstd::prelude::*;

verus! {

pub fn suma_it(V: &[i32]) -> (x: i32)
    ensures x == suma_vector(V, 0)
{
}

pub open spec fn suma_vector(V: &[i32], n: nat) -> i32
    recommends 0 <= n <= V.len()
{
    if n == V.len() { 0 } else { V[n as int] + suma_vector(V, n + 1) }
}

pub fn Main()
{
}

}