// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 &&
    a.len() == n &&
    (forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= n) &&
    (forall|i: int, j: int| 0 <= i < j < n ==> a[i] != a[j])
}

spec fn valid_output(n: int, result: int) -> bool {
    0 <= result <= n
}

spec fn reversed_array(a: Seq<int>) -> Seq<int>
    recommends a.len() >= 1
{
    Seq::new(a.len(), |i: int| a[a.len() - 1 - i])
}

spec fn has_increasing_pair(ar: Seq<int>) -> bool {
    exists|i: int| 1 <= i < ar.len() && #[trigger] ar[i] > ar[i-1]
}

spec fn min_index(ar: Seq<int>, n: int) -> int {
    0
}

spec fn correct_result(n: int, a: Seq<int>) -> int
    recommends valid_input(n, a)
{
    let ar = reversed_array(a);
    if has_increasing_pair(ar) {
        let min_i = min_index(ar, n);
        n - min_i
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_zero_index_lt_len(ar: Seq<int>) 
    requires ar.len() >= 1
    ensures 0 < ar.len()
{
}

proof fn lemma_prev_index_in_range(i: int, n: int)
    requires 1 <= i < n
    ensures 0 <= i-1 < n
{
}

proof fn lemma_all_unique_elements_in_range(ar: Seq<int>, i: int, j: int)
    requires 
        forall|k: int| 0 <= k < ar.len() ==> 1 <= ar[k] <= ar.len(),
        forall|k: int, l: int| 0 <= k < l < ar.len() ==> ar[k] != ar[l],
        0 <= i < ar.len(),
        i != j
    ensures j < 0 || j >= ar.len() || ar[i] != ar[j]
{
}

spec fn is_min_index(ar: Seq<int>, idx: int) -> bool {
    &&& 0 <= idx < ar.len()
    &&& forall|j: int| 0 <= j < ar.len() ==> ar[j] >= ar[idx]
}

proof fn lemma_min_index_exists(ar: Seq<int>) 
    requires ar.len() >= 1
    ensures exists|i: int| is_min_index(ar, i)
{
}

/* helper modified by LLM (iteration 5): type conversion helpers for usize to int */
proof fn lemma_usize_to_int_valid(n_usize: usize)
    ensures 0 <= n_usize as int
{
}

proof fn lemma_index_conversion_valid(i: usize, n: usize)
    requires i < n
    ensures 0 <= i as int < n as int
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures 
        valid_output(n as int, result as int) &&
        result as int == correct_result(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type conversion issues in invariants and assertions */
    let n_usize = n as usize;
    let mut ar_vec = a.clone();
    ar_vec.reverse();
    
    let mut has_increasing = false;
    
    if n_usize > 1 {
        let mut i = 1usize;
        while i < n_usize
            invariant 1 <= i <= n_usize
            decreases n_usize - i
        {
            if ar_vec[i] > ar_vec[i - 1] {
                has_increasing = true;
                break;
            }
            i += 1;
        }
    }
    
    if has_increasing {
        let mut min_idx = 0usize;
        let mut min_val = ar_vec[0];
        
        let mut i = 1usize;
        while i < n_usize
            invariant 
                1 <= i <= n_usize,
                0 <= min_idx < n_usize,
                min_val == ar_vec[min_idx],
                forall|j: int| 0 <= j < i as int ==> ar_vec[j] >= min_val
            decreases n_usize - i
        {
            if ar_vec[i] < min_val {
                min_idx = i;
                min_val = ar_vec[i];
            }
            i += 1;
        }
        
        let result = (n - min_idx as i8) as i8;
        result
    } else {
        0
    }
}
// </vc-code>


}

fn main() {}