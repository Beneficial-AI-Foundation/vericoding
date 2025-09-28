use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            n == a.len(),
            n > 0,
            forall|j: int| 0 <= j < i ==> {
                let left_idx = 2 * j + 1;
                let right_idx = 2 * j + 2;
                (left_idx < n) ==> (#[trigger] a[j] <= a[left_idx]) &&
                (right_idx < n) ==> (a[j] <= a[right_idx])
            }
        decreases n / 2 - i
    {
        let left_idx = 2 * i + 1;
        let right_idx = 2 * i + 2;
        
        if left_idx < n && a[i] > a[left_idx] {
            proof {
                assert(0 <= i < (n as int) / 2);
                assert(a[i as int] > a[left_idx as int] && left_idx < n);
            }
            return false;
        }
        
        if right_idx < n && a[i] > a[right_idx] {
            proof {
                assert(0 <= i < (n as int) / 2);
                assert(a[i as int] > a[right_idx as int] && right_idx < n);
            }
            return false;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == n / 2);
        assert(forall|j: int| 0 <= j < (n as int) / 2 ==> {
            let left_idx = 2 * j + 1;
            let right_idx = 2 * j + 2;
            (left_idx < n) ==> (#[trigger] a[j] <= a[left_idx]) &&
            (right_idx < n) ==> (a[j] <= a[right_idx])
        });
    }
    
    true
}
// </vc-code>

fn main() {}

}