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

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (m: i32)
    requires a.len() > 0
    ensures forall|k: int| 0 <= k < a.len() ==> m <= a[k]
    ensures exists|k: int| 0 <= k < a.len() && m == a[k]
// </vc-spec>
// <vc-code>
{
    let mut min = a[0];
    let mut i = 1;
    while i < a.len()
        invariant 0 <= i <= a.len()
        invariant forall|k: int| 0 <= k < i ==> min <= a@[k]
        invariant exists|k: int| 0 <= k < i && min == a@[k]
    {
        if a[i] < min {
            min = a[i];
        }
        i += 1;
    }
    min
}
// </vc-code>

fn main() {
}

}