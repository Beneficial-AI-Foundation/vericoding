use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_smaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires 
        a.len() == b.len(),
    ensures 
        result <==> forall|i: int| 0 <= i < a.len() ==> a[i] > b[i],
        !result <==> exists|i: int| 0 <= i < a.len() && a[i] <= b[i],
// </vc-spec>
// <vc-code>
{
    let violation = choose |i: int| #![trigger] (0 <= i < (a.len() as int) && a.index(i) <= b.index(i));
    if (violation < (a.len() as int)) && (a.index(violation) <= b.index(violation)) {
        assert(exists |i: int| #![trigger] (0 <= i < (a.len() as int) && a.index(i) <= b.index(i)));
        false
    } else {
        assert(forall |i: int| #![trigger] (0 <= i < (a.len() as int)) ==> a.index(i) > b.index(i));
        true
    }
}
// </vc-code>

fn main() {}

}