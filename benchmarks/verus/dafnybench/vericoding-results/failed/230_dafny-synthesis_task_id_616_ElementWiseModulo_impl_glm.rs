use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            (result@).len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> #![auto] result@[j] == a@[j] % b@[j],
        decreases(a@.len() - (i as int))
    {
        assert(i < b.len());
        assert(b[i] != 0);
        let e = a[i] % b[i];
        result.push(e);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {
}

}