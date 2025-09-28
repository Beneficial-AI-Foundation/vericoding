// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn even_index(k: int) -> int { 2 * k }
spec fn odd_index(k: int) -> int { 2 * k + 1 }
// </vc-helpers>

// <vc-spec>
fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)

    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
// </vc-spec>
// <vc-code>
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i as int <= arr.len() as int,
            out@.len() == 2 * (i as int),
            forall|k: int| 0 <= k < i as int ==> #[trigger] out@[2 * k] == elem,
            forall|k: int| 0 <= k < i as int ==> #[trigger] out@[2 * k + 1] == arr@[k],
        decreases (arr.len() - i)
    {
        out.push(elem);
        out.push(arr[i]);
        i += 1;
    }
    out
}
// </vc-code>

}
fn main() {}