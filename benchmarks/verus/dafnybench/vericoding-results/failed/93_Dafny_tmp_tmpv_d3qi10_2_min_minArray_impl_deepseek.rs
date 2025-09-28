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
proof fn min_array_proof(a: Seq<i32>, i: int, j: int, m: i32)
    requires
        0 <= i <= j < a.len(),
        forall|k: int| i <= k <= j ==> m <= a@[k],
        exists|k: int| i <= k <= j && m == a@[k]
    ensures
        forall|k: int| i <= k <= j ==> m <= a@[k],
        exists|k: int| i <= k <= j && m == a@[k]
{
}

proof fn min_array_merge_proof(a: Seq<i32>, i: int, mid: int, j: int, m1: i32, m2: i32, m: i32)
    requires
        0 <= i <= mid < j < a.len(),
        forall|k: int| i <= k <= mid ==> m1 <= a@[k],
        exists|k: int| i <= k <= mid && m1 == a@[k],
        forall|k: int| mid+1 <= k <= j ==> m2 <= a@[k],
        exists|k: int| mid+1 <= k <= j && m2 == a@[k],
        m == if m1 < m2 { m1 } else { m2 }
    ensures
        forall|k: int| i <= k <= j ==> m <= a@[k],
        exists|k: int| i <= k <= j && m == a@[k]
{
    assert forall|k: int| i <= k <= j implies m <= a@[k] by {
        if k <= mid {
            assert(m <= m1 <= a@[k]);
        } else {
            assert(m <= m2 <= a@[k]);
        }
    }
    
    if m == m1 {
        assert(exists|k: int| i <= k <= mid && m == a@[k]);
    } else {
        assert(exists|k: int| mid+1 <= k <= j && m == a@[k]);
    }
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
    let mut m = a[0];
    let n = a.len() as int;
    
    proof {
        assert(0 <= 0 < n);
        assert(m == a@[0]);
    }
    
    let mut i: usize = 1;
    while i < n as usize
        invariant
            0 < i as int <= n,
            forall|k: int| 0 <= k < i as int ==> m <= a@[k],
            exists|k: int| 0 <= k < i as int && m == a@[k]
    {
        let current = a[i];
        proof {
            assert(0 <= i as int < n);
            assert(current == a@[i as int]);
        }
        
        if current < m {
            m = current;
            proof {
                assert(m == a@[i as int]);
                assert forall|k: int| 0 <= k <= i as int implies m <= a@[k] by {
                    if k < i as int {
                        assert(forall|k: int| 0 <= k < i as int ==> m <= a@[k]);
                    } else {
                        assert(k == i as int);
                        assert(m == a@[i as int]);
                    }
                }
                assert(exists|k: int| 0 <= k <= i as int && m == a@[k]) by {
                    assert(m == a@[i as int]);
                }
            }
        } else {
            proof {
                assert(m <= current);
                assert forall|k: int| 0 <= k <= i as int implies m <= a@[k] by {
                    if k < i as int {
                        // Preserve existing invariant
                    } else {
                        assert(k == i as int);
                        assert(m <= current == a@[i as int]);
                    }
                }
                // The exists invariant is preserved since m hasn't changed
            }
        }
        
        i += 1;
    }
    
    m
}
// </vc-code>

fn main() {
}

}