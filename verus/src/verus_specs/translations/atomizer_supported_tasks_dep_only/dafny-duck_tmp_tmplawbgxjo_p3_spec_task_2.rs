use vstd::prelude::*;

verus! {

pub fn max(x: &[nat]) -> (y: nat)
    requires(
        x.len() > 0
    )
    ensures(|y: nat|
        forall|j: int| 0 <= j < x.len() ==> y >= x[j] &&
        exists|k: int| 0 <= k < x.len() && y == x[k]
    )
{
}

pub fn main()
{
}

}