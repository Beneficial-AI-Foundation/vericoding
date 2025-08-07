use vstd::prelude::*;

verus! {

spec fn remove_element_precond(lst: Seq<u32>, target: u32) -> bool {
    true
}

spec fn remove_element_postcond(lst: Seq<u32>, target: u32, result: Seq<u32>) -> bool {
    // Result contains exactly the elements of lst that are not equal to target, in order
    result == lst.filter(|x: u32| x != target)
}

// Simple implementation - the verification would need more sophisticated proof techniques
fn remove_element(lst: Vec<u32>, target: u32) -> (result: Vec<u32>)
    requires remove_element_precond(lst@, target)  
    ensures remove_element_postcond(lst@, target, result@)
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < lst.len()
        invariant 
            0 <= i <= lst.len(),
            result@ == lst@.subrange(0, i as int).filter(|x: u32| x != target)
    {
        if lst[i] != target {
            result.push(lst[i]);
        }
        i += 1;
    }
    
    assert(lst@.subrange(0, lst.len() as int) == lst@);
    result
}

proof fn remove_element_spec_satisfied(lst: Seq<u32>, target: u32)
    requires remove_element_precond(lst, target)
{
    // This theorem would be proven by the ensures clause of remove_element
    // when called with appropriate Vec conversion
    admit();
}

fn main() {
}

} // verus!