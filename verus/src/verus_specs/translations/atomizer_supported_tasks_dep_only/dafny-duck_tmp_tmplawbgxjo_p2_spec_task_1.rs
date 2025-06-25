use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> nat {
    if x < 0 { -x } else { x }
}

pub fn absx(x: &[i32]) -> (y: Vec<i32>)
    ensures
        y.len() == x.len(),
        forall|i: int| 0 <= i < y.len() ==> y[i] == abs(x[i] as int),
{
}

}