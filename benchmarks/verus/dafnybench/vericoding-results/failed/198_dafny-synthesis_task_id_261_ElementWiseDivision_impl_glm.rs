use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_division_basic(a: int, b: int)
    requires
        b != 0,
    ensures
        a / b * b + a % b == a,
{
}

proof fn lemma_division_nonnegative(a: int, b: int)
    requires
        b != 0,
        a >= 0 && b > 0,
    ensures
        a / b >= 0,
{
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
    seq(|i: int| a[i] / b[i], a.len())
}
// </vc-code>

fn main() {
}

}