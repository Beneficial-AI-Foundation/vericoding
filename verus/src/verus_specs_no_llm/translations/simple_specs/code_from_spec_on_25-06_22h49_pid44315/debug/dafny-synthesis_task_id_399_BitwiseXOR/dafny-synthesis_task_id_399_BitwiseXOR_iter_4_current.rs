use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn BitwiseXOR(a: Seq<u32>, b: Seq<u32>) -> (result: Seq<u32>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall |i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) ^ b.spec_index(i)
{
    let mut result = Seq::empty();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result.spec_index(j) == a.spec_index(j) ^ b.spec_index(j)
    {
        let a_val = a.spec_index(i as int);
        let b_val = b.spec_index(i as int);
        result = result.push(a_val ^ b_val);
        
        i = i + 1;
    }
    
    result
}

}