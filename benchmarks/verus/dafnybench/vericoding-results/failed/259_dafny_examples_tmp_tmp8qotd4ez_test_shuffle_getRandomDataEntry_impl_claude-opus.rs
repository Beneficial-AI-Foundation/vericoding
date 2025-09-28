use vstd::prelude::*;

verus! {

fn random(a: int, b: int) -> (r: int)
    ensures a <= b ==> a <= r <= b
{
    assume(false);
    a
}

spec fn set_of_seq<T>(s: Seq<T>) -> Set<T> {
    s.to_set()
}

// <vc-helpers>
proof fn seq_contains_to_set_contains<T>(s: Seq<T>, x: T)
    ensures s.contains(x) <==> set_of_seq(s).contains(x)
{
    assert(s.to_set().contains(x) <==> s.contains(x));
}

proof fn find_element_not_in_avoid<T>(work_list: Seq<T>, avoid_set: Seq<T>) -> (idx: nat)
    requires 
        work_list.len() > 0,
        set_of_seq(avoid_set).subset_of(set_of_seq(work_list)),
        set_of_seq(avoid_set) != set_of_seq(work_list),
    ensures 
        idx < work_list.len(),
        !avoid_set.contains(work_list[idx as int]),
{
    // Since avoid_set is a proper subset of work_list, there exists an element in work_list not in avoid_set
    let avoid_s = set_of_seq(avoid_set);
    let work_s = set_of_seq(work_list);
    
    assert(exists|x: T| work_s.contains(x) && !avoid_s.contains(x)) by {
        // This follows from avoid_s being a proper subset of work_s
    }
    
    let witness = choose|x: T| work_s.contains(x) && !avoid_s.contains(x);
    assert(work_list.contains(witness));
    assert(!avoid_set.contains(witness));
    
    // Find the index of witness in work_list
    let idx = choose|i: nat| i < work_list.len() && work_list[i as int] == witness;
    assert(idx < work_list.len());
    assert(work_list[idx as int] == witness);
    assert(!avoid_set.contains(work_list[idx as int]));
    idx
}
// </vc-helpers>

// <vc-spec>
fn get_random_data_entry<T: PartialEq + Clone>(m_work_list: &Vec<T>, avoid_set: &Vec<T>) -> (e: T)
    requires m_work_list.len() > 0
    ensures 
        set_of_seq(avoid_set@).subset_of(set_of_seq(m_work_list@)) && 
        set_of_seq(avoid_set@) != set_of_seq(m_work_list@) ==> !avoid_set@.contains(e),
        (forall |x: T| avoid_set@.contains(x) ==> m_work_list@.contains(x)) && 
        avoid_set@ != m_work_list@ ==> m_work_list@.contains(e)
// </vc-spec>
// <vc-code>
{
    let m_len = m_work_list.len();
    
    if set_of_seq(avoid_set@).subset_of(set_of_seq(m_work_list@)) && 
       set_of_seq(avoid_set@) != set_of_seq(m_work_list@) {
        // Need to find an element not in avoid_set
        let ghost idx_proof = find_element_not_in_avoid(m_work_list@, avoid_set@);
        proof {
            assert(idx_proof < m_work_list.len());
            assert(!avoid_set@.contains(m_work_list@[idx_proof as int]));
        }
        
        // Use random to get an index, but we'll loop until we find one not in avoid_set
        let mut idx: usize = 0;
        let mut found = false;
        
        while !found
            invariant
                0 <= idx <= m_work_list.len(),
                found ==> idx < m_work_list.len() && !avoid_set@.contains(m_work_list@[idx as int]),
        {
            let rand_int = random(0, (m_len - 1) as int);
            if 0 <= rand_int && rand_int < (m_len as int) {
                idx = rand_int as usize;
                
                // Check if this element is in avoid_set
                let mut in_avoid = false;
                let mut i: usize = 0;
                while i < avoid_set.len()
                    invariant
                        0 <= i <= avoid_set.len(),
                        in_avoid ==> exists|j: int| 0 <= j < i && avoid_set@[j] == m_work_list@[idx as int],
                        !in_avoid ==> forall|j: int| 0 <= j < i ==> avoid_set@[j] != m_work_list@[idx as int],
                {
                    if avoid_set[i] == m_work_list[idx] {
                        in_avoid = true;
                    }
                    i = i + 1;
                }
                
                if !in_avoid {
                    found = true;
                    proof {
                        assert(!avoid_set@.contains(m_work_list@[idx as int]));
                    }
                }
            }
        }
        
        let result = m_work_list[idx].clone();
        proof {
            assert(!avoid_set@.contains(result));
            assert(m_work_list@.contains(result));
        }
        result
    } else {
        // Just return any element
        let rand_int = random(0, (m_len - 1) as int);
        let idx = if 0 <= rand_int && rand_int < (m_len as int) {
            rand_int as usize
        } else {
            0usize
        };
        
        let result = m_work_list[idx].clone();
        proof {
            assert(m_work_list@.contains(result));
        }
        result
    }
}
// </vc-code>

fn main() {
}

}