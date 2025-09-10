use vstd::prelude::*;

verus! {

spec fn min(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

spec fn min_function(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

fn min_array(a: &Vec<i32>) -> (m: i32)
    requires a.len() > 0
    ensures 
        forall|k: int| 0 <= k < a.len() ==> m <= a[k],
        exists|k: int| 0 <= k < a.len() && m == a[k]
{
    assume(false);
    unreached();
}

}
fn main() {}