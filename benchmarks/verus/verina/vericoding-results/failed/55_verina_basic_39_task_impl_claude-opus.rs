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
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let len = l.len();
    if len == 0 {
        return Vec::new();
    }
    
    let effective_n = n % len;
    let mut result = Vec::new();
    
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let rotated_index = ((j - effective_n as int + len as int) % len as int) as int;
                #[trigger] result[j] == l[rotated_index]
            },
        decreases len - i
    {
        // Use usize arithmetic to avoid type errors
        let rotated_index = if i >= effective_n {
            i - effective_n
        } else {
            len - effective_n + i
        };
        result.push(l[rotated_index]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}