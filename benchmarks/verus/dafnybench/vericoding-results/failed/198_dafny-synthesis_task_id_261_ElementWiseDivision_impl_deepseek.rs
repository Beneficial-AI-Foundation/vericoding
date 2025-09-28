use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn division_lemma(a: int, b: int)
    requires
        b != 0,
    ensures
        a / b == a / b,
{
}

proof fn element_wise_division_helper(a: Seq<int>, b: Seq<int>, i: int)
    requires
        a.len() == b.len(),
        forall|j: int| 0 <= j < b.len() ==> b[j] != 0,
        0 <= i < a.len(),
    ensures
        b[i] != 0,
        a[i] / b[i] == a[i] / b[i],
{
    assert(b[i] != 0);
    division_lemma(a[i], b[i]);
}
// </vc-helpers>

// <vc-spec>
fn element_wise_division(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Seq::<int>::empty();
    let mut n: int = 0;
    while n < a.len()
        invariant
            n >= 0,
            n <= a.len(),
            result.len() == n,
            forall|i: int| 0 <= i < n ==> result[i] == a[i] / b[i],
        decreases a.len() - n,
    {
        proof { element_wise_division_helper(a, b, n); }
        result = result.push(a[n] / b[n]);
        n = n + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}