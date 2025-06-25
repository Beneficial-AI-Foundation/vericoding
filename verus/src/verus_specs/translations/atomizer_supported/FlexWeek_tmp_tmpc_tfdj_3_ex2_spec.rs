use vstd::prelude::*;

verus! {

spec fn abs(a: int) -> nat {
    if a < 0 { -a } else { a }
}

pub fn aba(a: &[i32]) -> (b: Vec<i32>)
    ensures
        a.len() == b.len(),
        forall|x: int| 0 <= x < b.len() ==> b[x as int] == abs(a[x as int]),
{
}

pub fn main() {
}

}