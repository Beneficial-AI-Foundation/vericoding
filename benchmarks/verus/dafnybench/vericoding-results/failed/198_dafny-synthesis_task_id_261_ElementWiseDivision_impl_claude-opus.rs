use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn element_wise_division(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// <vc-code>
{
    let mut result_vec: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    let a_vec = a.to_vec();
    let b_vec = b.to_vec();
    
    while i < a_vec.len()
        invariant
            a_vec@.len() == a.len(),
            b_vec@.len() == b.len(),
            i <= a_vec.len(),
            result_vec@.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> result_vec@[j] as int == a[j] / b[j],
    {
        let ai = a_vec[i];
        let bi = b_vec[i];
        assert(bi != 0) by {
            assert(0 <= i < b.len());
            assert(b[i as int] != 0);
            assert(b_vec@[i as int] == b[i as int]);
        }
        let quotient: i32 = ai / bi;
        result_vec.push(quotient);
        
        assert(result_vec@[i as int] as int == a[i as int] / b[i as int]) by {
            assert(result_vec@.len() == (i + 1) as nat);
            assert(result_vec@[i as int] == quotient);
            assert(ai as int == a[i as int]);
            assert(bi as int == b[i as int]);
            assert(quotient as int == (ai / bi) as int);
            assert((ai / bi) as int == (ai as int) / (bi as int));
        }
        
        i = i + 1;
    }
    
    let ghost result: Seq<int> = Seq::new(result_vec@.len(), |j: int| result_vec@[j] as int);
    
    proof {
        assert(result.len() == a.len()) by {
            assert(result_vec@.len() == a.len());
        }
        assert(forall|j: int| 0 <= j < result.len() ==> result[j] == a[j] / b[j]) by {
            assert(forall|j: int| 0 <= j < result_vec@.len() ==> result_vec@[j] as int == a[j] / b[j]);
            assert(forall|j: int| 0 <= j < result.len() ==> result[j] == result_vec@[j] as int);
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}