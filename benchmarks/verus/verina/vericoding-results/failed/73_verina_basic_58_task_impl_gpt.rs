// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple doubling function used optionally */
fn double_i32(x: i32) -> i32 { 2 * x }
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix int/usize mismatch and reason about last pushed element */
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            out.len() == i,
            i <= s.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] out@[j] == 2 * s@[j],
        decreases s.len() - i
    {
        let val: i32 = s[i];
        let doubled: i32 = 2 * val;
        let old_len = out.len();
        out.push(doubled);
        proof {
            assert(old_len == i);
            assert(out.len() == old_len + 1);
            assert(out@[old_len as int] == doubled);
            assert(val == s@[i as int]);
            assert forall|j: int| 0 <= j < old_len as int + 1 ==> #[trigger] out@[j] == 2 * s@[j] by {
                if j < old_len as int {
                    // preserved from the invariant
                } else {
                    assert(j == old_len as int);
                    assert(s@[j] == s@[i as int]);
                    assert(out@[j] == doubled);
                    assert(doubled == 2 * val);
                    assert(2 * val == 2 * s@[i as int]);
                }
            }
        }
        i += 1;
    }
    out
}
// </vc-code>

}
fn main() {}