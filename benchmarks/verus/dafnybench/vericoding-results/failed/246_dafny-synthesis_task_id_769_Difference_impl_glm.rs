use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j),
// </vc-spec>
// <vc-code>
{
    let mut result: Seq<int> = Seq::empty();
    let mut i: nat = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|x: int| result.contains(x) ==> (a.contains(x) && !b.contains(x)),
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
            forall|x: int| (exists|j: int| 0 <= j < i && a[j] == x) && !b.contains(x) ==> result.contains(x),
    {
        let x = a[i];
        if !b.contains(x) {
            if !result.contains(x) {
                result = result.push(x);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}