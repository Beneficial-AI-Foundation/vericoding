use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[cfg(feature = "trust_external_code")]
fn eq_int(x: int, y: int) -> bool {
    x == y
}
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
    let mut i: nat = 0;
    while (i as int) < a.len()
        invariant
            0 <= i as int,
            i as int <= a.len(),
            forall|k: int| 0 <= k < i as int ==> a[k] > b[k],
    {
        if a.index(i as int) <= b.index(i as int) {
            return false;
        }
        i = (i + 1) as nat;
    }
    true
}
// </vc-code>

fn main() {}

}