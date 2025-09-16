// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}

spec fn diff(s: Seq<(i32, i32)>) -> (ret: int) {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): replaced iterator methods with loops to avoid compilation error */
fn zip_halves_exec(v: Vec<i32>) -> Vec<(i32, i32)> {
    let n = v.len();
    let k = n / 2;
    let mut result = Vec::new();
    for i in 0..k {
        result.push((v[i], v[n - 1 - i]));
    }
    result
}

fn diff_exec(pairs: Vec<(i32, i32)>) -> usize {
    let mut count = 0;
    for (a, b) in pairs {
        if a != b {
            count += 1;
        }
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)

    requires
        v@.len() < usize::MAX,

    ensures
        change == diff(zip_halves(v@)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): using fixed helper functions (with loops) */
    let zipped = zip_halves_exec(v);
    let result = diff_exec(zipped);
    result
}
// </vc-code>

}
fn main() {}