use vstd::prelude::*;

verus! {

// <vc-helpers>
//
// </vc-helpers>

// <vc-spec>
fn difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j),
// </vc-spec>
// <vc-code>
{
    let mut result = Seq::empty();
    let a_len = a.len() as int;
    for i in 0..a_len {
        let elem = a.index(i as usize);
        if !b.contains(elem) && !result.contains(elem) {
            result = result.push(elem);
        }
    }
    result
}
// </vc-code>

fn main() {}

}