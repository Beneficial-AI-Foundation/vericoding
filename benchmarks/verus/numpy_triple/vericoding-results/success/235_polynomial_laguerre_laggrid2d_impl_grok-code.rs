// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn laggrid2d(x: Vec<f64>, y: Vec<f64>, c: Vec<Vec<f64>>) -> (result: Vec<Vec<f64>>)
    requires
        c@.len() > 0,
        c@.len() > 0 ==> c@[0].len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> #[trigger] c@[i].len() == c@[0].len(),
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == y@.len(),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x@.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == y@.len(),
        decreases x@.len() - i
    {
        let mut inner: Vec<f64> = Vec::new();
        let mut j = 0;
        while j < y.len()
            invariant
                result@.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == y@.len(),
                j <= y@.len(),
                inner@.len() == j,
            decreases y@.len() - j
        {
            inner.push(0.0);
            j = j + 1;
        }
        result.push(inner);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}