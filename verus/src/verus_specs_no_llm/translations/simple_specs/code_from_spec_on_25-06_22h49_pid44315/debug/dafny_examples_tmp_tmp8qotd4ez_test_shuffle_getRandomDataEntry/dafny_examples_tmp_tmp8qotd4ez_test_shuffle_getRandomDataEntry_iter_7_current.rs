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
fn is_in_avoid_set<T: PartialEq>(avoid_set: &Seq<T>, elem: &T) -> (result: bool)
    ensures result == seq_contains(*avoid_set, *elem)
{
    let mut i: usize = 0;
    while i < avoid_set.len()
        invariant 
            0 <= i <= avoid_set.len(),
            forall|k: int| 0 <= k < i ==> avoid_set[k] != *elem,
    {
        if avoid_set[i as int] == *elem {
            return true;
        }
        i += 1;
    }
    false
}

fn get_random_data_entry<T: Copy + PartialEq>(m_work_list: &Vec<T>, avoid_set: Seq<T>) -> (e: T)
    requires 
        m_work_list.len() > 0,
        exists|i: int| 0 <= i < m_work_list.len() && 
            !seq_contains(avoid_set, m_work_list[i])
    ensures
        !seq_contains(avoid_set, e)
{
    // Find first element not in avoid_set
    let mut i: usize = 0;
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
        assert(seq_contains(avoid_set, m_work_list[i as int]));
        i += 1;
    }
    
    // This should never be reached due to the precondition
    proof {
        // The loop terminated, so i == m_work_list.len()
        // From invariant: all elements 0..i are in avoid_set
        // But precondition guarantees existence of element not in avoid_set
        // This is a contradiction
        let witness_idx = choose|j: int| 0 <= j < m_work_list.len() && 
            !seq_contains(avoid_set, m_work_list[j]);
        assert(0 <= witness_idx < m_work_list.len());
        assert(!seq_contains(avoid_set, m_work_list[witness_idx]));
        assert(seq_contains(avoid_set, m_work_list[witness_idx])); // from loop invariant
        assert(false);
    }
    
    // Unreachable code - we've proven false above
    arbitrary()
}

}