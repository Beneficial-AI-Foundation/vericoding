use vstd::prelude::*;

verus! {

spec fn Fat(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * Fat((n - 1) as nat) }
}

pub fn Fatorial(n: nat) -> (f: nat)
    ensures f == Fat(n)
{
    unimplemented!()
}

}