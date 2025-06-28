use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementWiseModulo(a: Vec<int>, b: Vec<int>) -> (result: Vec<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b.spec_index(i) != 0
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) % b.spec_index(i)
{
    let mut result = Vec::new();
    let mut index: usize = 0;
    
    while index < a.len()
        invariant
            0 <= index <= a.len(),
            a.len() == b.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) % b.spec_index(i),
            forall|i: int| 0 <= i < b.len() ==> b.spec_index(i) != 0
    {
        let a_val = a[index];
        let b_val = b[index];
        
        // In Verus, we need to be explicit about the modulo operation
        // The modulo operation is well-defined for non-zero divisors
        proof {
            assert(b_val != 0);
        }
        
        let mod_value = a_val % b_val;
        result.push(mod_value);
        
        proof {
            assert(result.len() == index + 1);
            assert(result.spec_index(index as int) == mod_value);
            assert(mod_value == a_val % b_val);
            assert(a_val == a.spec_index(index as int));
            assert(b_val == b.spec_index(index as int));
            assert(result.spec_index(index as int) == a.spec_index(index as int) % b.spec_index(index as int));
        }
        
        index += 1;
    }
    
    result
}

}