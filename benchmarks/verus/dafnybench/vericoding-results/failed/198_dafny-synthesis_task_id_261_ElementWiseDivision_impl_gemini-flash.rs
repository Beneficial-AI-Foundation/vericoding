use vstd::prelude::*;

verus! {

// <vc-helpers>
fn seq_div(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i && i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[i] / b[i],
{
    let mut result: Seq<int> = Seq::new(a.len(), |i: int| a.index(i));
    let mut i: nat = 0;
    while (i as int) < (a.len() as int)
        invariant
            0 <= i,
            i <= a.len(),
            result.len() == a.len(),
            forall|j: int| 0 <= j && j < i as int ==> result.index(j) == a.index(j) / b.index(j),
    {
        result = result.update(i as int, a.index(i as int) / b.index(i as int));
        i = i + 1;
    }
    result
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
    seq_div(a, b)
}
// </vc-code>

fn main() {
}

}