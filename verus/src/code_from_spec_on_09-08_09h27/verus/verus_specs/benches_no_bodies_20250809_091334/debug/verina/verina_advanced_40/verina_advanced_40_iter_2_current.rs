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

// Helper lemma to prove properties about max_of_list_helper
proof fn max_of_list_helper_correct(lst: Seq<nat>)
    requires lst.len() > 0,
    ensures max_of_list_postcond(lst, max_of_list_helper(lst)),
    decreases lst.len(),
{
    if lst.len() == 1 {
        // Base case: single element list
        let result = lst.index(0);
        assert(lst.contains(result));
        assert(forall|x: nat| lst.contains(x) ==> x <= result) by {
            assert(forall|x: nat| lst.contains(x) ==> x == result);
        }
    } else {
        // Recursive case
        let head = lst.index(0);
        let tail = lst.subrange(1, lst.len() as int);
        let max_tail = max_of_list_helper(tail);
        
        // Recursive call establishes properties for tail
        max_of_list_helper_correct(tail);
        assert(max_of_list_postcond(tail, max_tail));
        
        let result = if head > max_tail { head } else { max_tail };
        
        // Prove result is in the list
        if head > max_tail {
            assert(lst.contains(head));
        } else {
            assert(tail.contains(max_tail));
            assert(lst.contains(max_tail)) by {
                assert(forall|i: int| 0 <= i < tail.len() ==> lst.index(i + 1) == tail.index(i));
            }
        }
        
        // Prove result is maximum
        assert(forall|x: nat| lst.contains(x) ==> x <= result) by {
            assert(forall|x: nat| lst.contains(x) ==> (x == head || tail.contains(x)));
            if head > max_tail {
                assert(forall|x: nat| tail.contains(x) ==> x <= max_tail);
                assert(max_tail < head);
            } else {
                assert(head <= max_tail);
                assert(forall|x: nat| tail.contains(x) ==> x <= max_tail);
            }
        }
    }
}

// Main theorem proving the specification is satisfied
proof fn max_of_list_spec_satisfied(lst: Seq<nat>)
    requires max_of_list_precond(lst),
    ensures max_of_list_postcond(lst, max_of_list(lst)),
{
    max_of_list_helper_correct(lst);
}

fn main() {
    // Example usage with verification
    /* code modified by LLM (iteration 1): fixed invalid nat suffix in number literals, using u32 instead */
    let v = vec![3u32, 1u32, 4u32, 1u32, 5u32, 9u32];
    let seq_v = v@;
    
    proof {
        max_of_list_spec_satisfied(seq_v);
    }
    
    println!("Vector: {:?}", v);
    println!("Maximum value exists and is correctly computed by spec function");
}

}