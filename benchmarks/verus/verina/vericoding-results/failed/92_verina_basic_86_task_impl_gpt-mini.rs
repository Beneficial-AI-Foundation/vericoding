// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): compute source index modulo length */
spec fn src_index(i: int, offset: int, len: int) -> int requires len > 0 { (i + offset) % len }
// </vc-helpers>

// <vc-spec>
fn rotate(a: &Vec<i32>, offset: int) -> (result: Vec<i32>)
    requires offset >= 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = (i + offset) % (a.len() as int);
            #[trigger] result[i] == a[src_idx]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implement rotate using spec-level indexing to avoid casting int to usize */
    let n = a.len();
    if n == 0 {
        return Vec::new();
    }
    let mut result = Vec::<i32>::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n,
                  result.len() == i,
                  forall|j: int| 0 <= j < (i as int) ==> result@[j] == a@[((j + offset) % (n as int))],
        decreases n - i
    {
        let src_idx = (i as int + offset) % (n as int);
        let val = a@[src_idx];
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}