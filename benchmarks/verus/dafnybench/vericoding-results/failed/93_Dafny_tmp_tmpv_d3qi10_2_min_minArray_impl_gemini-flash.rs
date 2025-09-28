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
#[verifier(external_body)]
#[spec]
fn i32_to_int(i: i32) -> int {
    i as int
}
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (m: i32)
    requires a.len() > 0
    ensures forall|k: int| 0 <= k < a.len() ==> m <= a[k]
    ensures exists|k: int| 0 <= k < a.len() && m == a[k]
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 1;
    let mut m: i32 = a[0];

    while i < a.len()
        invariant
            0 < i as int && i as int <= a.len(),
            forall|k: int| 0 <= k && k < i as int ==> i32_to_int(m) <= i32_to_int(a[k]),
            exists|k: int| 0 <= k && k < i as int && i32_to_int(m) == i32_to_int(a[k]),
    {
        if i32_to_int(a[i]) < i32_to_int(m) {
            m = a[i];
        }
        i = i + 1;
    }
    m
}
// </vc-code>

fn main() {
}

}