use vstd::prelude::*;

verus! {

// Precondition: list must be non-empty  
spec fn max_of_list_precond(lst: Seq<u32>) -> bool {
    lst.len() > 0
}

// Postcondition: result is in the list and is the maximum element
spec fn max_of_list_postcond(lst: Seq<u32>, result: u32) -> bool {
    (exists|i: int| 0 <= i < lst.len() && lst[i] == result) &&
    (forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result)
}

// Executable version using Vec
fn max_of_list(lst: &Vec<u32>) -> (result: u32)
    requires 
        max_of_list_precond(lst@),
    ensures 
        max_of_list_postcond(lst@, result),
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}

} // verus!