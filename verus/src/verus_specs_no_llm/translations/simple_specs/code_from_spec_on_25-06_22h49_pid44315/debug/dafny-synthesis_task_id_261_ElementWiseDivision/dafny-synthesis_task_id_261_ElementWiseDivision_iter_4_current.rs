use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementWiseDivision(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b.spec_index(i) != 0
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) / b.spec_index(i)
{
    let mut result = Seq::empty();
    let mut index: usize = 0;
    
    while index < a.len()
        invariant
            0 <= index <= a.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) / b.spec_index(i)
    {
        // Convert usize to int for indexing
        let index_int = index as int;
        
        // Use array indexing syntax for executable code access
        let a_val = a[index_int];
        let b_val = b[index_int];
        
        // Assert that b_val is not zero (required for division)
        assert(b_val != 0) by {
            assert(0 <= index_int < b.len());
        };
        
        let div_result = a_val / b_val;
        result = result.push(div_result);
        
        // Proof that the invariant is maintained
        assert(result.spec_index(index_int) == a.spec_index(index_int) / b.spec_index(index_int)) by {
            assert(result.spec_index(index_int) == div_result);
            assert(div_result == a_val / b_val);
            assert(a_val == a.spec_index(index_int));
            assert(b_val == b.spec_index(index_int));
        };
        
        index = index + 1;
    }
    
    result
}

}