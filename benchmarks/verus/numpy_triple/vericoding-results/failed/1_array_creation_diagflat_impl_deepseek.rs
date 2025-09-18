// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove problematic nat conversion and use proper ghost function */
spec fn len_as_nat(v: Vec<f32>) -> nat { v.len() as nat }
// </vc-helpers>

// <vc-spec>
fn diagflat(v: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == v.len() * v.len(),
        forall|i: int| 0 <= i < v.len() ==> #[trigger] result[i * v.len() + i] == v[i],
        forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> #[trigger] result[i * v.len() + j] == 0.0f32
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by removing nat conversion and using proper ghost code */
{
    let n = v.len();
    let mut result = Vec::new();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i * n,
            forall|k: int| 0 <= k < i as int ==> #[trigger] result[(k * n as int + k) as usize] == v[k as usize],
            forall|k: int, j: int| 0 <= k < i as int && 0 <= j < n as int && k != j ==> #[trigger] result[(k * n as int + j) as usize] == 0.0f32
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                result.len() == i * n + j,
                forall|k: int| 0 <= k < i as int ==> #[trigger] result[(k * n as int + k) as usize] == v[k as usize],
                forall|k: int, l: int| 0 <= k < i as int && 0 <= l < n as int && k != l ==> #[trigger] result[(k * n as int + l) as usize] == 0.0f32,
                forall|l: int| 0 <= l < j as int ==> #[trigger] result[((i as int) * n as int + l) as usize] == if i as int == l { v[i as usize] } else { 0.0f32 }
            decreases n - j
        {
            let val = if i == j { v[i] } else { 0.0f32 };
            result.push(val);
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}