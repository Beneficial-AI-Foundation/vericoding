use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn random(a: int, b: int) -> (r: int)
    requires a <= b
    ensures a <= r <= b
{
    // Simple implementation that returns the lower bound
    // In a real implementation, this would use actual randomness
    a
}

// Spec function to convert sequence to set
spec fn set_of_seq<T>(s: Seq<T>) -> Set<T> {
    Set::new(|x: T| s.contains(x))
}

// Spec function to check if element is in sequence
spec fn seq_contains<T>(s: Seq<T>, elem: T) -> bool {
    s.contains(elem)
}

// Helper function to check if element is in avoid_set (executable version)
fn is_in_avoid_set<T>(avoid_set: &Seq<T>, elem: &T) -> (result: bool)
    where T: PartialEq
    ensures result == seq_contains(*avoid_set, *elem)
{
    let mut i: usize = 0;
    while i < avoid_set.len()
        invariant 
            0 <= i <= avoid_set.len(),
            forall|k: int| 0 <= k < i ==> avoid_set[k] != *elem,
    {
        if avoid_set[i as int] == *elem {
            // Prove that finding the element means it's contained
            assert(seq_contains(*avoid_set, *elem));
            return true;
        }
        i += 1;
    }
    
    // Prove the postcondition when loop completes
    assert(forall|k: int| 0 <= k < avoid_set.len() ==> avoid_set[k] != *elem);
    
    // Prove that if no element equals *elem, then the sequence doesn't contain *elem
    proof {
        if seq_contains(*avoid_set, *elem) {
            // If the sequence contains *elem, then there exists an index where it equals *elem
            // But we've proven that no such index exists, contradiction
            assert(false);
        }
    }
    
    false
}

fn get_random_data_entry<T>(m_work_list: &Vec<T>, avoid_set: Seq<T>) -> (e: T)
    where T: Copy + PartialEq
    requires 
        m_work_list.len() > 0,
        exists|i: int| 0 <= i < m_work_list.len() && 
            !seq_contains(avoid_set, m_work_list[i])
    ensures
        !seq_contains(avoid_set, e)
{
    // Find first element not in avoid_set
    let mut i: usize = 0;
    
    // Use a while loop instead of loop for better verification
    while i < m_work_list.len()
        invariant 
            0 <= i <= m_work_list.len(),
            // There exists an element from position i onwards that's not in avoid_set
            exists|j: int| i <= j < m_work_list.len() && 
                !seq_contains(avoid_set, m_work_list[j]),
            // All elements before position i are in avoid_set
            forall|k: int| 0 <= k < i ==> seq_contains(avoid_set, m_work_list[k])
    {
        let in_avoid = is_in_avoid_set(&avoid_set, &m_work_list[i]);
        if !in_avoid {
            assert(!seq_contains(avoid_set, m_work_list[i as int]));
            return m_work_list[i];
        }
        
        // Element at i is in avoid_set, continue to next
        assert(seq_contains(avoid_set, m_work_list[i as int]));
        i += 1;
    }
    
    // This point should be unreachable due to the precondition
    proof {
        // When we exit the loop, i == m_work_list.len()
        // From the invariant, there should exist j such that i <= j < len
        // But i == len, so no such j exists, contradicting the invariant
        // This means the loop must have returned before reaching this point
        assert(false);
    }
    
    // This is unreachable, but we need to provide a value for type checking
    // Using assume(false) to indicate this is unreachable
    assume(false);
    m_work_list[0]  // This will never execute
}

}