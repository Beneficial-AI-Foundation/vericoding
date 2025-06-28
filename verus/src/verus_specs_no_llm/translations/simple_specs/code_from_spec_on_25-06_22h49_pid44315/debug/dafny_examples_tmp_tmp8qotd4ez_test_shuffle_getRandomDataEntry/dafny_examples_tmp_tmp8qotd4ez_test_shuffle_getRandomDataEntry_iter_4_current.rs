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
            exists|j: int| 0 <= j < m_work_list.len() && 
                !seq_contains(avoid_set, m_work_list[j]),
            forall|k: int| 0 <= k < i ==> seq_contains(avoid_set, m_work_list[k])
    {
        if !seq_contains(avoid_set, m_work_list[i]) {
            return m_work_list[i];
        }
        i += 1;
    }
    
    // This should never be reached due to the precondition
    // The precondition guarantees there exists an element not in avoid_set
    // The loop invariant says all elements from 0 to i-1 are in avoid_set
    // When we exit the loop, i == m_work_list.len(), so all elements are in avoid_set
    // This contradicts the precondition
    assert(false) by {
        assert(i == m_work_list.len());
        assert(exists|j: int| 0 <= j < m_work_list.len() && 
            !seq_contains(avoid_set, m_work_list[j]));
        assert(forall|k: int| 0 <= k < i ==> seq_contains(avoid_set, m_work_list[k]));
        assert(forall|k: int| 0 <= k < m_work_list.len() ==> seq_contains(avoid_set, m_work_list[k]));
    }
    
    // This line is unreachable, but needed for compilation
    unreached()
}

}