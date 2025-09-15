// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let n = a.len();
    let mut result = Vec::with_capacity(n);
    for i in 0..n {
        let src_idx = (i as int + offset) % (n as int);
        result.push(a[src_idx as usize]);
    }
    result
}
// </vc-code>

}
fn main() {}