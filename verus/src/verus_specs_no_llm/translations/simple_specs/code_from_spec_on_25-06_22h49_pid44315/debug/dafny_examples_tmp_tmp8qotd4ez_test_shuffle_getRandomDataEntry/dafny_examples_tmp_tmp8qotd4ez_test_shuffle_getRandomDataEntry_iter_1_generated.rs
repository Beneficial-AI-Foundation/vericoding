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
spec fn set_of_seq<T>(s: Seq<T>) -> Set<T>;
{
}

// Spec function to check if element is in sequence
spec fn seq_contains<T>(s: Seq<T>, elem: T) -> bool;
{
}

fn get_random_data_entry<T>(m_work_list: &Vec<T>, avoid_set: Seq<T>) -> (e: T)
    requires 
        m_work_list.len() > 0,
        exists|i: int| 0 <= i < m_work_list.len() && 
            !seq_contains(avoid_set, m_work_list[i])
    ensures
        !seq_contains(avoid_set, e)
{
    // Find first element not in avoid_set
    let mut i = 0;
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
    m_work_list[0]
}

}