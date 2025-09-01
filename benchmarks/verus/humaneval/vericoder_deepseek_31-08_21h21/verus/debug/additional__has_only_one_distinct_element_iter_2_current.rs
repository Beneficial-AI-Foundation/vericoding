use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn distinct_proof(a: &[i32], i: int, j: int) 
    requires 
        0 <= i < a.len() as int,
        0 <= j < a.len() as int,
        a[i as usize] != a[j as usize],
    ensures
        exists|ii: int, jj: int| 
            0 <= ii < a.len() as int && 0 <= jj < a.len() as int && a[ii as usize] != a[jj as usize],
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if a.len() <= 1 {
        return true;
    }
    
    let mut all_equal = true;
    let mut i: usize = 0;
    
    while i < a.len() {
        invariant
            0 <= i <= a.len(),
            all_equal ==> forall|k: int, l: int| 0 <= k < i as int && 0 <= l < i as int ==> a[k as usize] == a[l as usize],
            !all_equal ==> exists|k: int, l: int| 0 <= k < i as int && 0 <= l < i as int && a[k as usize] != a[l as usize],
        {
            if i == 0 {
                i = i + 1;
                continue;
            }
            
            if a[i] != a[0] {
                all_equal = false;
                break;
            }
            
            i = i + 1;
        }
    }
    
    if all_equal {
        proof {
            assert forall|ii: int, jj: int| 0 <= ii < a.len() as int && 0 <= jj < a.len() as int implies a[ii as usize] == a[jj as usize] by {
                assert(a[ii as usize] == a[0]);
                assert(a[jj as usize] == a[0]);
            };
        }
        true
    } else {
        proof {
            let k = 0;
            let l = i as int - 1;
            assert(0 <= k < a.len() as int);
            assert(0 <= l < a.len() as int);
            assert(a[k as usize] != a[l as usize]);
            distinct_proof(a, k, l);
        }
        false
    }
}
// </vc-code>

fn main() {}
}