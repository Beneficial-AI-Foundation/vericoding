use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn xor_properties()
    ensures
        forall|a: u32, b: u32| (#[trigger](a ^ b)) == a ^ b,
{
    assert forall|a: u32, b: u32| (#[trigger](a ^ b)) == a ^ b by {
        assert(a ^ b == a ^ b);
    }
}
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
    let mut result = Vec::<u32>::new();
    let n: nat = a.len();
    let mut i: nat = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: nat| j < i ==> result@[j] == a[j] ^ b[j],
    {
        result.push(a[i] ^ b[i]);
        i = i + 1;
    }
    Seq::from_vec(result)
}
// </vc-code>

fn main() {}

}