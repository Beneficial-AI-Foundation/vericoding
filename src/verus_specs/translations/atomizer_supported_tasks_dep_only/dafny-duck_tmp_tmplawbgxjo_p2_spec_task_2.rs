use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> nat {
    if x < 0 { -x } else { x }
}

pub fn absx(x: &[int]) -> (y: Vec<int>)
    ensures
        y.len() == x.len(),
        forall|i: int| 0 <= i < y.len() ==> y[i] == abs(x[i]),
{
}

pub fn main() {
}

}