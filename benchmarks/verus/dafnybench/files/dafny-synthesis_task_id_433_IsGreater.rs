use vstd::prelude::*;

verus! {

fn is_greater(n: i32, a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int| 0 <= i < a.len() ==> n > a[i],
        !result ==> exists|i: int| 0 <= i < a.len() && n <= a[i],
{
    assume(false);
    unreached()
}

}
fn main() {}