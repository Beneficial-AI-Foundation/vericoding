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

fn get_random_data_entry<T: Copy>(m_work_list: &Vec<T>, avoid_set: Seq<T>) -> (e: T)
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
            exists|j: int| i <= j < m_work_list.len() && 
                !seq_contains(avoid_set, m_work_list[j])
    {
        if !seq_contains(avoid_set, m_work_list[i]) {
            return m_work_list[i];
        }
        i += 1;
    }
    
    // This should never be reached due to the precondition
    proof {
        // The loop invariant guarantees that there exists j >= i such that
        // !seq_contains(avoid_set, m_work_list[j]), but we've exited the loop
        // with i == m_work_list.len(), which means no such j exists.
        // This contradicts our loop invariant.
        assert(false) by {
            assert(i == m_work_list.len());
            assert(exists|j: int| i <= j < m_work_list.len() && 
                !seq_contains(avoid_set, m_work_list[j]));
            // No j can satisfy i <= j < i, so we have a contradiction
        }
    }
    
    // This line is unreachable, but needed for compilation
    m_work_list[0]
}

}