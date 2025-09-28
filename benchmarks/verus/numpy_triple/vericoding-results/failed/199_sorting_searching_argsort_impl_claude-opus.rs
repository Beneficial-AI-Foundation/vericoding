// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Simplify invariants to avoid trigger inference issues */
    let n = a.len();
    let mut result: Vec<usize> = Vec::new();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] < n,
            forall|j: int, k: int| 0 <= j < k < i ==>
                a[#[trigger] result[j] as int] <= a[#[trigger] result[k] as int],
            forall|j: int, k: int| 0 <= j < k < i &&
                a[#[trigger] result[j] as int] == a[#[trigger] result[k] as int] ==>
                result[j] < result[k],
        decreases n - i
    {
        let mut min_idx: usize = 0;
        let mut min_val: i8 = i8::MAX;
        let mut found = false;
        
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                found ==> min_idx < n,
                found ==> min_val == a[min_idx as int],
            decreases n - j
        {
            let mut already_used = false;
            let mut k: usize = 0;
            while k < i
                invariant
                    k <= i,
                    already_used <==> exists|l: int| 0 <= l < k && result[l] == j,
                decreases i - k
            {
                if result[k] == j {
                    already_used = true;
                }
                k = k + 1;
            }
            
            if !already_used {
                if !found || a[j] < min_val || (a[j] == min_val && j < min_idx) {
                    min_idx = j;
                    min_val = a[j];
                    found = true;
                }
            }
            j = j + 1;
        }
        
        assert(found);
        result.push(min_idx);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}