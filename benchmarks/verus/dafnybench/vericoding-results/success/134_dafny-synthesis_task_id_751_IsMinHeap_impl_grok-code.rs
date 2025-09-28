use vstd::prelude::*;

verus! {

// <vc-helpers>
// Ensure all auxiliary definitions and proofs are handled within the code for this fix.
// </vc-helpers>

// <vc-spec>
fn is_min_heap(a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0
    ensures 
        result ==> forall|i: int| 0 <= i < (a.len() as int) / 2 ==> {
            let left_idx = 2 * i + 1;
            let right_idx = 2 * i + 2;
            (left_idx < a.len()) ==> (#[trigger] a[i as int] <= a[left_idx]) &&
            (right_idx < a.len()) ==> (a[i as int] <= a[right_idx])
        },
        !result ==> exists|i: int| 0 <= i < (a.len() as int) / 2 && {
            let left_idx = 2 * i + 1;
            let right_idx = 2 * i + 2;
            (#[trigger] a[i as int] > a[left_idx] && left_idx < a.len()) ||
            (a[i as int] > a[right_idx] && right_idx < a.len())
        }
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 0;
    #[verifier::loop_isolation(false)]
    while i < n / 2
        invariant
            0 <= i as int <= (n as int) / 2,
            forall |j: int| 0 <= j < (i as int) ==> {
                let left_j: int = 2 * j + 1;
                let right_j: int = 2 * j + 2;
                (left_j < n as int) ==> #[trigger] a@[j] <= a@[left_j] &&
                (right_j < n as int) ==> #[trigger] a@[j] <= a@[right_j]
            }
        decreases ((n as int) / 2 - (i as int))
    {
        let left: usize = 2 * i + 1;
        let right: usize = 2 * i + 2;
        if left < n && a[i] > a[left] {
            return false;
        }
        if right < n && a[i] > a[right] {
            return false;
        }
        proof {
            let left_j = 2 * (i as int) + 1;
            let right_j = 2 * (i as int) + 2;
            assert(!(left_j < n as int) || a@[i as int] <= a@[left_j]);
            assert(!(right_j < n as int) || a@[i as int] <= a@[right_j]);
        }
        i += 1;
    }
    return true;
}
// </vc-code>

fn main() {}

}