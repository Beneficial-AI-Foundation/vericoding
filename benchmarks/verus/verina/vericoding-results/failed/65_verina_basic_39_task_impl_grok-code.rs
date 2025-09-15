// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed to use exec types for modular arithmetic instead of ghost int */
fn calculate_rotated_index(i: usize, n_mod: usize, len: usize) -> usize {
    (i + len - n_mod) % len
}
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
    /* code modified by LLM (iteration 5): Completed rotation using exec helper fn */
    let len = l.len();
    if len == 0 {
        Vec::new()
    } else {
        let n_mod = n % len;
        let mut result = Vec::with_capacity(len);
        for i in 0..len {
            let rotated_index = calculate_rotated_index(i, n_mod, len);
            result.push(l[rotated_index]);
        }
        result
    }
}
// </vc-code>

}
fn main() {}