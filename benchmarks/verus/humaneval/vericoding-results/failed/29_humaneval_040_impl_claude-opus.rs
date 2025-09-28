// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_triple_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int, k: int| 0 <= i < j < k < l.len() && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triples_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_triple_sum_to_zero(l@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added trigger annotations for quantifiers */
    let n = l.len();
    if n < 3 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < n - 2
        invariant
            i <= n - 2,
            forall|i_p: int, j_p: int, k_p: int| 
                0 <= i_p < j_p < k_p < l@.len() && i_p < i ==> 
                l@.map(|idx, x: i8| x as int)[i_p] + l@.map(|idx, x: i8| x as int)[j_p] + l@.map(|idx, x: i8| x as int)[k_p] != 0,
        decreases n - 2 - i
    {
        let mut j: usize = i + 1;
        while j < n - 1
            invariant
                i < j <= n - 1,
                i < n - 2,
                forall|j_p: int, k_p: int| 
                    i < j_p < k_p < l@.len() && j_p < j ==> 
                    l@.map(|idx, x: i8| x as int)[i as int] + l@.map(|idx, x: i8| x as int)[j_p] + l@.map(|idx, x: i8| x as int)[k_p] != 0,
            decreases n - 1 - j
        {
            let mut k: usize = j + 1;
            while k < n
                invariant
                    j < k <= n,
                    i < j < n - 1,
                    i < n - 2,
                    forall|k_p: int| 
                        #[trigger] (l@.map(|idx, x: i8| x as int)[k_p])
                        j < k_p < l@.len() && k_p < k ==> 
                        l@.map(|idx, x: i8| x as int)[i as int] + l@.map(|idx, x: i8| x as int)[j as int] + l@.map(|idx, x: i8| x as int)[k_p] != 0,
                decreases n - k
            {
                let sum: i32 = l[i] as i32 + l[j] as i32 + l[k] as i32;
                if sum == 0 {
                    assert(l@.map(|idx, x: i8| x as int)[i as int] + l@.map(|idx, x: i8| x as int)[j as int] + l@.map(|idx, x: i8| x as int)[k as int] == 0);
                    assert(0 <= i < j < k < l@.len());
                    assert(has_triple_sum_to_zero(l@.map(|idx, x: i8| x as int)));
                    return true;
                }
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    assert(forall|i_p: int, j_p: int, k_p: int| 
        0 <= i_p < j_p < k_p < l@.len() ==> 
        l@.map(|idx, x: i8| x as int)[i_p] + l@.map(|idx, x: i8| x as int)[j_p] + l@.map(|idx, x: i8| x as int)[k_p] != 0);
    assert(!has_triple_sum_to_zero(l@.map(|idx, x: i8| x as int)));
    false
}
// </vc-code>


}

fn main() {}