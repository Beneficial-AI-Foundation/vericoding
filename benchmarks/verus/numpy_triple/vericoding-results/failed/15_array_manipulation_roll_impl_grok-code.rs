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
    /* code modified by LLM (iteration 3): Computed normalized index using exec i32 operations to avoid spec types in exec code */
    let mut result: Vec<T> = Vec::new();
    if a.len() == 0 {
        result
    } else {
        let len = a.len();
        let shift_i32 = shift;
        let len_i32 = len as i32;
        let mut i = 0;
        while i < len
            invariant
                result.len() == i,
                forall |j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[normalize_index(j, shift as int, len as int)],
            decreases len - i
        {
            let i_i32 = i as i32;
            let src_i32 = (i_i32 - shift_i32) % len_i32;
            let src_i32_normalized = (src_i32 + len_i32) % len_i32;
            let src_idx_usize = src_i32_normalized as usize;
            assert(0 <= src_idx_usize < len);
            result.push(a[src_idx_usize]);
            i += 1;
        }
        result
    }
}
// </vc-code>


}
fn main() {}