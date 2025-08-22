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
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result@[j] as int == (a@[j] as int) * (a@[j] as int) * (a@[j] as int)
    {
        let cube = a[i] * a[i] * a[i];
        result.push(cube);
        i += 1;
    }
    
    result
}

spec fn cube_elements_postcond(a: Seq<i32>, result: Seq<i32>) -> bool {
    &&& result.len() == a.len()
    &&& forall|i: int| #![auto] 0 <= i < a.len() ==> result[i] as int == (a[i] as int) * (a[i] as int) * (a[i] as int)
}

fn main() {}

}