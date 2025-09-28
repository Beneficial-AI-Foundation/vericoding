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
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[j] % b@[j],
            forall|j: int| 0 <= j < b@.len() ==> b@[j] != 0,
    {
        assert(i < b.len()) by {
            assert(i < a.len());
            assert(a.len() == b.len());
        }
        assert(b@[i as int] != 0) by {
            assert(0 <= i as int < b@.len());
            assert(forall|j: int| 0 <= j < b@.len() ==> b@[j] != 0);
        }
        
        let mod_val = a[i] % b[i];
        result.push(mod_val);
        
        assert(result@.len() == i + 1);
        assert(result@[i as int] == mod_val);
        assert(mod_val == a@[i as int] % b@[i as int]);
        assert(forall|j: int| 0 <= j < i + 1 ==> #[trigger] result@[j] == a@[j] % b@[j]) by {
            assert(forall|j: int| 0 <= j < i ==> result@[j] == a@[j] % b@[j]);
            assert(result@[i as int] == a@[i as int] % b@[i as int]);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}