// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate_right(l: &Vec<i32>, n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> {
            let len = l.len() as int;
            let rotated_index = ((i - n as int + len) % len) as int;
            #[trigger] result[i] == l[rotated_index]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added a 'decreases' clause to the while loop to prove termination. */
    let len = l.len();
    if len == 0 {
        return Vec::new();
    }

    let mut result = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            result.len() == i,
        decreases len - i
    {
        // The previous attempt's indexing logic is safe for `usize` (no underflow)
        // and correctly computes the rotated source index.
        let n_mod = n % len;
        let source_idx = (i + len - n_mod) % len;
        result.push(l[source_idx]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}