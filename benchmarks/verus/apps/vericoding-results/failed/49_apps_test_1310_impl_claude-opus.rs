// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn xor_range(arr: Seq<u32>, i: int, j: int) -> u32;

spec fn valid_input(arr: Seq<u32>) -> bool {
    arr.len() > 0
}

spec fn is_max_xor_subarray(arr: Seq<u32>, result: u32) -> bool
    recommends valid_input(arr)
{
    exists|i: int, j: int| 0 <= i <= j < arr.len() && result == xor_range(arr, i, j) &&
    forall|i1: int, j1: int| 0 <= i1 <= j1 < arr.len() ==> 
        (xor_range(arr, i1, j1) as int) <= (result as int)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added uninterp marker and fixed loop invariant logic */
#[verifier::uninterp]
spec fn xor_range(arr: Seq<u32>, i: int, j: int) -> u32;

fn compute_xor_range(arr: &Vec<u32>, i: usize, j: usize) -> (result: u32)
    requires
        i <= j,
        j < arr.len()
    ensures
        result == xor_range(arr@, i as int, j as int)
{
    let mut xor = 0u32;
    let mut k = i;
    while k <= j
        invariant
            i <= k,
            k <= j + 1,
            j < arr.len(),
            k <= j ==> xor == xor_range(arr@, i as int, (k - 1) as int),
            k == j + 1 ==> xor == xor_range(arr@, i as int, j as int)
        decreases j + 1 - k
    {
        xor = xor ^ arr[k];
        k = k + 1;
    }
    xor
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<u32>) -> (result: u32)
    requires valid_input(arr@)
    ensures is_max_xor_subarray(arr@, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Maintained original nested loop structure */
    let n = arr.len();
    let mut max_xor = 0u32;
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i,
            i <= n,
            n == arr.len(),
            n > 0,
            forall|i1: int, j1: int| 0 <= i1 && i1 < i as int && i1 <= j1 && j1 < n as int ==> 
                (xor_range(arr@, i1, j1) as int) <= (max_xor as int)
        decreases n - i
    {
        let mut j = i;
        while j < n
            invariant
                0 <= i,
                i <= j,
                j <= n,
                n == arr.len(),
                n > 0,
                forall|i1: int, j1: int| 0 <= i1 && i1 < i as int && i1 <= j1 && j1 < n as int ==> 
                    (xor_range(arr@, i1, j1) as int) <= (max_xor as int),
                forall|j1: int| i as int <= j1 && j1 < j as int ==> 
                    (xor_range(arr@, i as int, j1) as int) <= (max_xor as int)
            decreases n - j
        {
            let current_xor = compute_xor_range(&arr, i, j);
            if current_xor > max_xor {
                max_xor = current_xor;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    max_xor
}
// </vc-code>


}

fn main() {}