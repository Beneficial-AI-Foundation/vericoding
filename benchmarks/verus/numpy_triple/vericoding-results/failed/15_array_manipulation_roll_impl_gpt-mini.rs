// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove normalize_index returns value in [0, n) */
proof fn normalize_index_range(i: int, shift: int, n: int)
    requires
        n > 0,
    ensures
        0 <= normalize_index(i, shift, n) < n,
{
    proof {
        let src = i - shift;
        let m = src % n;
        if m < 0 {
            assert(normalize_index(i, shift, n) == m + n);
            assert(m + n >= 0);
            assert(m + n < n);
        } else {
            assert(normalize_index(i, shift, n) == m);
            assert(m >= 0);
            assert(m < n);
        }
    }
}

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
    /* code modified by LLM (iteration 5): use non-ghost integer arithmetic (i32/usize) to compute indices */
    // impl-start
    let n = a.len();
    if n == 0 {
        return a;
    }
    let n_i32 = n as i32;
    let shift_i32 = shift;
    let shift_mod_i32 = ((shift_i32 % n_i32) + n_i32) % n_i32;
    let shift_mod = shift_mod_i32 as usize;
    let mut a_opt: Vec<Option<T>> = a.into_iter().map(|x| Some(x)).collect();
    let mut result: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
        decreases n - i
    {
        let idx = (i + n - shift_mod) % n;
        let v = a_opt[idx].take().unwrap();
        result.push(v);
        i += 1;
    }
    result
    // impl-end
}

// </vc-code>


}
fn main() {}