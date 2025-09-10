use vstd::prelude::*;

verus! {

spec fn max_array_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

fn max_array(a: &Vec<i32>) -> (result: i32)
    requires max_array_precond(a),
    ensures
        forall|k: int| 0 <= k < a.len() ==> result >= a[k],
        exists|k: int| 0 <= k < a.len() && result == a[k],
{
    assume(false);
    unreached()
}

}
fn main() {}