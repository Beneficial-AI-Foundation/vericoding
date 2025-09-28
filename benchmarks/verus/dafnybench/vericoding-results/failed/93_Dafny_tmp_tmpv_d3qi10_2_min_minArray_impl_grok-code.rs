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
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (m: i32)
    requires a.len() > 0
    ensures forall|k: int| 0 <= k < a.len() ==> m <= a[k]
    ensures exists|k: int| 0 <= k < a.len() && m == a[k]
// </vc-spec>
// <vc-code>
{
    let mut m: i32 = a[0];
    proof {
        let mut m_idx: int = 0;
    }
    let mut i: usize = 1;
    while i < a.len()
        invariant
            i <= a.len()
        invariant
            forall |k: int| { 0 <= k < i ==> m <= a@[k] }
        invariant
            a@[m_idx] == m
        invariant
            0 <= m_idx < i
    {
        if a[i] < m {
            m = a[i];
            proof {
                m_idx = i as int;
            }
        }
        i += 1;
    }
    assert(forall |k: int| { 0 <= k < a.len() ==> m <= a@[k] } );
    m
}
// </vc-code>

fn main() {
}

}