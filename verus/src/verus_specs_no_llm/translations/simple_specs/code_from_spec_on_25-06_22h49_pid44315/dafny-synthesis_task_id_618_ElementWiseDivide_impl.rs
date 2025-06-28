use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementWiseDivide(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b.spec_index(i) != 0
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) / b.spec_index(i)
{
    let mut result_vec: Vec<int> = Vec::new();
    let mut index: usize = 0;
    let a_vec = a.to_vec();
    let b_vec = b.to_vec();
    
    while index < a.len()
        invariant
            0 <= index <= a.len(),
            result_vec.len() == index,
            a_vec@ == a,
            b_vec@ == b,
            forall|i: int| 0 <= i < index ==> result_vec@.spec_index(i) == a.spec_index(i) / b.spec_index(i)
    {
        proof {
            assert(0 <= index < a.len());
            assert(0 <= index < b.len());
            assert(b.spec_index(index as int) != 0);
            assert(a_vec@.spec_index(index as int) == a.spec_index(index as int));
            assert(b_vec@.spec_index(index as int) == b.spec_index(index as int));
        }
        
        let a_val = a_vec[index];
        let b_val = b_vec[index];
        let div_result = a_val / b_val;
        result_vec.push(div_result);
        
        proof {
            assert(result_vec@.spec_index(index as int) == div_result);
            assert(div_result == a.spec_index(index as int) / b.spec_index(index as int));
        }
        
        index = index + 1;
    }
    
    result_vec@
}

}