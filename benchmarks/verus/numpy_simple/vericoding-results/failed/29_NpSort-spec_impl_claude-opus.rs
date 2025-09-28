// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn multiset_count<T>(s: Seq<T>, x: T) -> nat {
    s.filter(|y| y == x).len()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed swap operation to properly update sorted vector */
    let mut sorted = a.clone();
    let n = sorted.len();
    
    if n == 0 {
        return sorted;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            sorted.len() == a.len(),
            sorted.len() == n,
            forall|x: i8| multiset_count(sorted@, x) == multiset_count(a@, x),
            forall|j: int, k: int| 0 <= j < k < i ==> sorted[j] <= sorted[k],
            forall|j: int, k: int| 0 <= j < i && i <= k < n ==> sorted[j] <= sorted[k],
        decreases n - i
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        
        while j < n
            invariant
                i < n,
                i + 1 <= j <= n,
                i <= min_idx < j,
                sorted.len() == n,
                forall|k: int| i <= k < j ==> sorted[min_idx as int] <= sorted[k],
            decreases n - j
        {
            if sorted[j] < sorted[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let temp = sorted[i];
            let mut sorted_new = sorted.clone();
            sorted_new = sorted_new.set(i, sorted[min_idx]);
            sorted_new = sorted_new.set(min_idx, temp);
            sorted = sorted_new;
        }
        
        i = i + 1;
    }
    
    sorted
}
// </vc-code>


}
fn main() {}