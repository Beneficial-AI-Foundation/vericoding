use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementWiseModulo(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
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
        
        // Prove that b_val is non-zero
        proof {
            assert(b_val == b.spec_index(index as int));
            assert(0 <= index < b.len());
            assert(b.spec_index(index as int) != 0);
            assert(b_val != 0);
        }
        
        let mod_value = a_val % b_val;
        result.push(mod_value);
        
        proof {
            let old_result_len = result.len();
            assert(old_result_len == index);
            assert(result.len() == index + 1);
            assert(result.spec_index(index as int) == mod_value);
            assert(mod_value == a_val % b_val);
            assert(a_val == a.spec_index(index as int));
            assert(b_val == b.spec_index(index as int));
            assert(result.spec_index(index as int) == a.spec_index(index as int) % b.spec_index(index as int));
            
            // Maintain the invariant for all previously computed elements
            assert(forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) % b.spec_index(i));
        }
        
        index += 1;
    }
    
    proof {
        assert(index == a.len());
        assert(result.len() == a.len());
        assert(forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) % b.spec_index(i));
    }
    
    result
}

}