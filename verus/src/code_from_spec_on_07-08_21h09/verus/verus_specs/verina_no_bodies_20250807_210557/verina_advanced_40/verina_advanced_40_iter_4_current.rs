use vstd::prelude::*;

verus! {

// Precondition: list is non-empty  
spec fn max_of_list_precond(lst: Seq<nat>) -> bool {
    lst.len() > 0
}

// Helper function to find maximum of a list (spec function)
spec fn max_of_list_helper(lst: Seq<nat>) -> nat
    decreases lst.len()
{
    if lst.len() == 0 {
        0  // dummy value, should not be reached with precondition
    } else if lst.len() == 1 {
        lst.index(0)
    } else {
        let head = lst.index(0);
        let tail = lst.subrange(1, lst.len() as int);
        let max_tail = max_of_list_helper(tail);
        if head > max_tail { head } else { max_tail }
    }
}

// Main function (spec function)
spec fn max_of_list(lst: Seq<nat>) -> nat
    recommends max_of_list_precond(lst)
{
    max_of_list_helper(lst)
}

// Postcondition specification
spec fn max_of_list_postcond(lst: Seq<nat>, result: nat) -> bool {
    lst.contains(result) && 
    (forall|x: nat| lst.contains(x) ==> x <= result)
}

// Helper lemma for subrange containment
proof fn subrange_contains_lemma(lst: Seq<nat>, x: nat)
    requires lst.len() > 1
    requires lst.subrange(1, lst.len() as int).contains(x)
    ensures lst.contains(x)
{
    /* code modified by LLM (iteration 1): fixed missing braces and proper syntax */
    let tail = lst.subrange(1, lst.len() as int);
    assert(exists|i: int| 1 <= i < lst.len() && lst.index(i) == x);
}

// Helper lemma for the recursive case
proof fn max_helper_properties(lst: Seq<nat>)
    requires lst.len() > 0
    ensures lst.contains(max_of_list_helper(lst))
    ensures forall|x: nat| lst.contains(x) ==> x <= max_of_list_helper(lst)
    decreases lst.len()
{
    /* code modified by LLM (iteration 1): fixed missing braces and proper syntax */
    if lst.len() == 1 {
        // Base case: single element
        assert(lst.contains(lst.index(0)));
        assert(forall|x: nat| lst.contains(x) ==> x == lst.index(0));
    } else {
        // Recursive case
        let head = lst.index(0);
        let tail = lst.subrange(1, lst.len() as int);
        let max_tail = max_of_list_helper(tail);
        
        // Recursive call establishes properties for tail
        max_helper_properties(tail);
        
        if head > max_tail {
            // head is the maximum
            assert(lst.contains(head));
            assert(forall|x: nat| lst.contains(x) ==> {
                if x == head {
                    x <= head
                } else {
                    tail.contains(x) && x <= max_tail && max_tail < head
                }
            });
        } else {
            // max_tail is the maximum
            assert(tail.contains(max_tail));
            assert(lst.contains(max_tail)) by {
                subrange_contains_lemma(lst, max_tail);
            };
            assert(forall|x: nat| lst.contains(x) ==> {
                if x == head {
                    x <= max_tail
                } else {
                    tail.contains(x) && x <= max_tail
                }
            });
        }
    }
}

// Main theorem proving the specification is satisfied
proof fn max_of_list_spec_satisfied(lst: Seq<nat>)
    requires max_of_list_precond(lst)
    ensures max_of_list_postcond(lst, max_of_list(lst))
{
    /* code modified by LLM (iteration 1): fixed missing braces and proper syntax */
    max_helper_properties(lst);
}

fn main() {
    // Example usage demonstrating the max_of_list function
    let example_seq = seq![3nat, 1nat, 4nat, 1nat, 5nat, 9nat, 2nat];
    
    proof {
        max_of_list_spec_satisfied(example_seq);
    }
    
    // The specification is satisfied for this example
    assert(max_of_list_precond(example_seq));
    assert(max_of_list_postcond(example_seq, max_of_list(example_seq)));
}

}