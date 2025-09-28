// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove mod returns nonnegative remainder */
proof fn mod_nonneg(len: int, x: int)
    requires
        len > 0
    ensures
        0 <= x % len,
        x % len < len
{
    proof {
        assert(0 <= x % len);
        assert(x % len < len);
    }
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
    /* code modified by LLM (iteration 2): implement rotation by computing rotated indices and pushing elements */
    let m = l.len();
    let mut result: Vec<i32> = Vec::new();
    if m == 0 {
        result
    } else {
        let len_i = m as int;
        let n_i = n as int;
        let mut i: usize = 0;
        while i < m
            invariant
                result.len() == i,
                i <= m,
                forall|j: int| 0 <= j && j < i as int ==> result[j as usize] == l[(((j - n_i + len_i) % len_i) as usize)],
            decreases m - i
        {
            let idx = (((i as int - n_i + len_i) % len_i) as usize);
            result.push(l[idx]);
            i += 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}