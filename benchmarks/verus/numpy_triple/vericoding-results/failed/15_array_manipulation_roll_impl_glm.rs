// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn normalize_index(i: int, shift: int, n: int) -> int {
    let src_idx = i - shift;
    let mod_result = src_idx % n;
    if mod_result < 0 { mod_result + n } else { mod_result }
}

fn roll<T>(a: Vec<T>, shift: i32) -> (result: Vec<T>)
    ensures
        result.len() == a.len(),
        a.len() == 0 ==> result@ == a@,
        a.len() > 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == a[normalize_index(i, shift as int, a.len() as int)]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replace extend with loops */
    if a.len() == 0 {
        return vec![];
    }
    let n = a.len();
    let n_u64 = n as u64;
    let shift_mod = if shift >= 0 {
        (shift as u64) % n_u64
    } else {
        let neg_shift = -shift;
        let r = (neg_shift as u64) % n_u64;
        if r == 0 {
            0
        } else {
            n_u64 - r
        }
    } as usize;
    let split_index = n - shift_mod;
    let part1 = a.split_off(split_index);
    let mut result = Vec::with_capacity(n);
    for elem in part1 {
        result.push(elem);
    }
    for elem in a {
        result.push(elem);
    }
    result
}
// </vc-code>


}
fn main() {}