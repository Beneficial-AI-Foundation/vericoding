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
    let n = a.len();
    let mut i: nat = 0;
    while (i < n)
        invariant { i <= n }
        invariant { forall |j: int| 0 <= j < i ==> a[j] > b[j] }
    {
        if a@[i] <= b@[i] {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

fn main() {}

}