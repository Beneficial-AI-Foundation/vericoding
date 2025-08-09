use vstd::prelude::*;

verus! {

spec fn cube_elements_precond(a: Seq<i32>) -> bool {
    true
}

fn cube_elements(a: Vec<i32>) -> (result: Vec<i32>)
    requires cube_elements_precond(a@),
    ensures cube_elements_postcond(a@, result@),
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

spec fn cube_elements_postcond(a: Seq<i32>, result: Seq<i32>) -> bool {
    &&& result.len() == a.len()
    &&& forall|i: int| #![auto] 0 <= i < a.len() ==> result[i] as int == (a[i] as int) * (a[i] as int) * (a[i] as int)
}

fn main() {}

}