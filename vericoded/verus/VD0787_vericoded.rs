// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 2): added trigger to loop invariant to fix verification error */
    let mut i: usize = 0;
    let n = a.len();
    while i < n / 2
        invariant
            n == a.len(),
            0 <= i <= n / 2,
            forall|j: int| 0 <= j < (i as int) ==> {
                let left_idx = 2 * j + 1;
                let right_idx = 2 * j + 2;
                (left_idx < n as int) ==> (#[trigger] a.view()[j] <= a.view()[left_idx]) &&
                (right_idx < n as int) ==> (a.view()[j] <= a.view()[right_idx])
            },
        decreases (n / 2) - i
    {
        let left_idx = 2 * i + 1;
        if left_idx < n {
            if a[i] > a[left_idx] {
                return false;
            }
        }

        let right_idx = 2 * i + 2;
        if right_idx < n {
            if a[i] > a[right_idx] {
                return false;
            }
        }
        
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}