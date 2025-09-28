use vstd::prelude::*;

verus! {

// <vc-helpers>
// Updated helpers section: no changes needed as helpers were empty and issue is in code section.
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    let len = a.len();
    proof {
        assert_by(a.len() as int == len as int, { });
    }
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == a@[j] as int % b@[j] as int,
        decreases len - i
    {
        assert(i < len);
        assert(b@[i as int] != 0);
        proof {
            assert(a@[i as int] as int % b@[i as int] as int == a[i] % b[i]);
        }
        result.push(a[i] % b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}