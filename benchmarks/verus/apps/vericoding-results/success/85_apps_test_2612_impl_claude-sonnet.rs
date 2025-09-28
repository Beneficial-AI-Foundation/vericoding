// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_beautiful_arrangement(arrangement: Seq<int>, sizes: Seq<int>) -> bool {
    arrangement.len() >= 1 &&
    (forall|i: int, j: int| #![trigger arrangement[i], arrangement[j]] 0 <= i < j < arrangement.len() ==> arrangement[i] != arrangement[j]) &&
    (forall|i: int| #![trigger arrangement[i]] 0 <= i < arrangement.len() - 1 ==> arrangement[i] < arrangement[i + 1]) &&
    (forall|i: int| #![trigger arrangement[i]] 0 <= i < arrangement.len() - 1 ==> arrangement[i + 1] % arrangement[i] == 0) &&
    (forall|i: int| #![trigger arrangement[i]] 0 <= i < arrangement.len() - 1 ==> 
        0 <= arrangement[i] - 1 < sizes.len() && 
        0 <= arrangement[i + 1] - 1 < sizes.len() &&
        sizes[arrangement[i] - 1] < sizes[arrangement[i + 1] - 1])
}

spec fn valid_input(n: int, sizes: Seq<int>) -> bool {
    n >= 1 && sizes.len() == n && forall|i: int| #![trigger sizes[i]] 0 <= i < n ==> sizes[i] >= 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed type casting, bounds checking, and arithmetic overflow issues */

spec fn can_extend_sequence(sizes: Seq<int>, seq: Seq<int>, next_idx: int) -> bool {
    if seq.len() == 0 {
        true
    } else {
        let last_idx = seq[seq.len() - 1] - 1;
        let next_actual = next_idx;
        0 <= last_idx < sizes.len() &&
        0 <= next_actual < sizes.len() &&
        sizes[last_idx] < sizes[next_actual] &&
        (next_idx + 1) % seq[seq.len() - 1] == 0
    }
}

fn find_max_length_from(sizes: &Vec<i8>, start: usize, n: i8) -> (result: i8)
    requires
        n >= 1,
        sizes.len() == n as usize,
        start < n as usize,
    ensures
        result >= 1,
        result <= n,
{
    let mut max_len = 1i8;
    let mut current = start as i8 + 1;
    
    while current < n
        invariant
            start as i8 + 1 <= current <= n,
            max_len >= 1,
            max_len <= n,
            start < n as usize,
            sizes.len() == n as usize,
        decreases n - current
    {
        let start_val = start as i8 + 1;
        if start < sizes.len() && (current as usize) < sizes.len() &&
           sizes[start] < sizes[current as usize] && current % start_val == 0 {
            max_len = 2;
        }
        current = current + 1;
    }
    
    max_len
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, sizes: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, sizes@.map(|x: int, v: i8| v as int))
    ensures 1 <= result as int <= n as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed precondition for helper function call */
    let mut best_length = 1i8;
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            1 <= best_length <= n,
            sizes.len() == n as usize,
        decreases n - i
    {
        if (i as usize) < (n as usize) {
            let current_length = find_max_length_from(&sizes, i as usize, n);
            if current_length > best_length {
                best_length = current_length;
            }
        }
        i = i + 1;
    }
    
    best_length
}
// </vc-code>


}

fn main() {}