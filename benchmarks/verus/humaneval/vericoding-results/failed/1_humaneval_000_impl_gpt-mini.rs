// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(numbers: Seq<int>, threshold: int) -> bool {
    true
}

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

spec fn has_close_elements(numbers: Seq<int>, threshold: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < numbers.len() && abs_diff(numbers[i], numbers[j]) < threshold
}

spec fn seq_map_to_int(numbers: Seq<i8>) -> Seq<int> {
        numbers.map(|_i: int, x: i8| x as int)
}
    

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): relate seq_map_to_int index to original vec element */
proof fn seq_map_index_eq(numbers: Vec<i8>, i: int)
    requires 0 <= i && i < numbers@.len()
    ensures seq_map_to_int(numbers@)@[i] == (numbers@)@[i] as int
{
    reveal(seq_map_to_int);
    assert(seq_map_to_int(numbers@)@[i] == (numbers@)@[i] as int);
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements_impl(numbers: Vec<i8>, threshold: i8) -> (result: bool)
    requires valid_input(seq_map_to_int(numbers@), threshold as int)
    ensures result == has_close_elements(seq_map_to_int(numbers@), threshold as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): runtime pairwise search with invariant and proof of equivalence */
    let n = numbers.len();
    let mut k: usize = 0;
    let mut found: bool = false;
    let mut pf: usize = 0;
    let mut qf: usize = 0;
    while k < n * n
        invariant
            0 <= (k as int) && (k as int) <= numbers@.len() * numbers@.len(),
            found == exists|p: int, q: int| 0 <= p && p < numbers@.len() && 0 <= q && q < numbers@.len() && p < q && (p * numbers@.len() + q) < (k as int) && abs_diff(seq_map_to_int(numbers@)@[p], seq_map_to_int(numbers@)@[q]) < (threshold as int),
        decreases numbers@.len() * numbers@.len() - (k as int)
    {
        let p = k / n;
        let q = k % n;
        if p < q {
            let ai = numbers[p] as i32;
            let aj = numbers[q] as i32;
            let thr = threshold as i32;
            if (ai - aj).abs() < thr {
                found = true;
                pf = p;
                qf = q;
            }
        }
        k = k + 1;
    }
    proof {
        // If we found a pair at runtime, produce the corresponding spec witness
        if found {
            let p_i: int = pf as int;
            let q_i: int = qf as int;
            seq_map_index_eq(numbers, p_i);
            seq_map_index_eq(numbers, q_i);
            assert(abs_diff(seq_map_to_int(numbers@)@[p_i], seq_map_to_int(numbers@)@[q_i]) < threshold as int);
            assert(exists|i: int, j: int| i == p_i && j == q_i && 0 <= i && i < j && j < numbers@.len() && abs_diff(seq_map_to_int(numbers@)@[i], seq_map_to_int(numbers@)@[j]) < threshold as int);
        } else {
            // If not found, use the loop invariant at termination to show no such pair exists
            // At loop exit k == n*n, hence the invariant characterizes all possible pairs
            assert(!(exists|i: int, j: int| 0 <= i && i < j && j < numbers@.len() && abs_diff(seq_map_to_int(numbers@)@[i], seq_map_to_int(numbers@)@[j]) < threshold as int));
        }
    }
    found
}
// </vc-code>


}

fn main() {}