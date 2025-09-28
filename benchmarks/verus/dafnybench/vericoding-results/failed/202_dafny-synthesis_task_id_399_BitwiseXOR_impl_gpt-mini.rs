use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn bitwise_xor(a: Seq<u32>, b: Seq<u32>) -> (result: Seq<u32>)
    requires
        a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] ^ b[i],
// </vc-spec>
// <vc-code>
{
    let n: nat = a.len();
    let mut v: Vec<u32> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant i <= n;
        invariant v@.len() == i;
        invariant forall|j: nat| j < i ==> v@[j] == a@[j] ^ b@[j];
        decreases n - i;
    {
        let x: u32 = a@[i] ^ b@[i];
        v.push(x);
        i = i + 1;
    }
    v.into_seq()
}
// </vc-code>

fn main() {}

}