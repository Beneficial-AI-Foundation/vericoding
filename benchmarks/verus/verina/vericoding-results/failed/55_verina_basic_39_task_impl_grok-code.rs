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
    /* code modified by LLM (iteration 5): Implemented rotation using usize arithmetic to avoid using ghost types like int in executable code, with conditional index calculation. */
    if l.is_empty() {
        return Vec::new();
    }
    let len = l.len();
    let effective_shift = n % len;
    let mut result = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let len_int = l.len() as int;
                let shift_int = effective_shift as int;
                let idx = ((j - shift_int) % len_int + len_int) % len_int;
                result[j] == l[idx]
            },
        decreases len - i
    {
        let idx = if i >= effective_shift { i - effective_shift } else { i + len - effective_shift };
        result.push(l[idx]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}