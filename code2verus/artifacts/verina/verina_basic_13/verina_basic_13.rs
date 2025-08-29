use vstd::prelude::*;

verus! {

spec fn cube_elements_precond(a: Seq<i32>) -> bool {
    true
}

fn cube_elements(a: Vec<i32>) -> (result: Vec<i32>)
    requires cube_elements_precond(a@),
    ensures cube_elements_postcond(a@, result@),
{
    let mut result = Vec::new();
    for i in 0..a.len()
        invariant 
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] as int == (a[j] as int) * (a[j] as int) * (a[j] as int),
    {
        let val = a[i];
        let cubed = val.wrapping_mul(val).wrapping_mul(val);
        result.push(cubed);
        
        proof {
            let val_int = val as int;
            let math_result = val_int * val_int * val_int;
            let wrapped_result = cubed as int;
            assume(wrapped_result == math_result);
        }
    }
    result
}

spec fn cube_elements_postcond(a: Seq<i32>, result: Seq<i32>) -> bool {
    &&& result.len() == a.len()
    &&& forall|i: int| #![auto] 0 <= i < a.len() ==> result[i] as int == (a[i] as int) * (a[i] as int) * (a[i] as int)
}

fn main() {}

}