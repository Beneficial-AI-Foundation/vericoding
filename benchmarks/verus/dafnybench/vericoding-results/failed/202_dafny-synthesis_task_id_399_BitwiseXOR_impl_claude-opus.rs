use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> result@[j] == a[j] ^ b[j],
    {
        let xor_val = a[i as int] ^ b[i as int];
        result.push(xor_val);
        
        assert(result@.len() == (i + 1) as nat);
        assert(result@[i as int] == a[i as int] ^ b[i as int]);
        
        i = i + 1;
    }
    
    result@
}
// </vc-code>

fn main() {}

}