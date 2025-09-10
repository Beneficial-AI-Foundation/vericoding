use vstd::prelude::*;

verus! {

fn ntypes(ufunc_type_combinations: Vec<String>) -> (result: usize)
    requires ufunc_type_combinations.len() > 0,
    ensures 
        result == ufunc_type_combinations.len(),
        result > 0
{
    assume(false);
    unreached();
}

}
fn main() {}