use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<i32>::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == (i as int),
            forall|k: int| 0 <= k < i ==> #[trigger] result[k] == a[k],
            i <= a.len(),
        decreases
            a.len() - i as int,
    {
        result.push(a[i]);
        i += 1;
    }
    let mut j = 0;
    while j < b.len()
        invariant
            result.len() == (a.len() + j) as int,
            forall|k: int| 0 <= k < a.len() ==> #[trigger] result[k] == a[k],
            forall|k: int| 0 <= k < j ==> #[trigger] result[a.len() + k] == b[k],
            j <= b.len(),
        decreases
            b.len() - j as int,
    {
        result.push(b[j]);
        j += 1;
    }
    result
}
// </vc-code>

fn main() {}
}