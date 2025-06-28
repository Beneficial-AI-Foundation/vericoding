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
            return true;
        }
        i += 1;
    }
    
    // When loop completes, we've checked all elements and none equal *elem
    assert(forall|k: int| 0 <= k < avoid_set.len() ==> avoid_set[k] != *elem);
    
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
    
    while i < m_work_list.len()
        invariant 
            0 <= i <= m_work_list.len(),
            // All elements before position i are in avoid_set
            forall|k: int| 0 <= k < i ==> seq_contains(avoid_set, m_work_list[k]),
            // There still exists an element from the original requirement
            exists|j: int| 0 <= j < m_work_list.len() && 
                !seq_contains(avoid_set, m_work_list[j])
    {
        let in_avoid = is_in_avoid_set(&avoid_set, &m_work_list[i]);
        if !in_avoid {
            return m_work_list[i];
        }
        
        i += 1;
    }
    
    // This point is unreachable due to the precondition
    // The precondition guarantees there exists an element not in avoid_set
    // But our loop invariant says all elements we've checked are in avoid_set
    // Since we've checked all elements (i == len), we have a contradiction
    unreached()
}

}