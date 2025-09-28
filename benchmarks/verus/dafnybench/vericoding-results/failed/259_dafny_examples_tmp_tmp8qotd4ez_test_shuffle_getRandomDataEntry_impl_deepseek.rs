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
spec fn seq_to_set_subset<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    s1.to_set().subset_of(s2.to_set())
}

proof fn lemma_seq_subset_implies_len<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.to_set().subset_of(s2.to_set()),
        s1.to_set() != s2.to_set()
    ensures
        s1.len() < s2.len()
{
}

proof fn lemma_seq_eq_set_implies_eq_len<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.to_set() == s2.to_set()
    ensures
        s1.len() == s2.len()
{
}

spec fn count_non_avoided<T>(work_list: Seq<T>, avoid_set: Seq<T>) -> nat
    recommends avoid_set.to_set().subset_of(work_list.to_set())
{
    (work_list.len() as nat) - (avoid_set.len() as nat)
}

proof fn lemma_non_avoided_positive<T>(work_list: Seq<T>, avoid_set: Seq<T>)
    requires
        work_list.len() > 0,
        avoid_set.to_set().subset_of(work_list.to_set()),
        avoid_set.to_set() != work_list.to_set()
    ensures
        count_non_avoided(work_list, avoid_set) > 0
{
}

spec fn index_of_non_avoided<T>(work_list: Seq<T>, avoid_set: Seq<T>, idx: int) -> bool
    recommends 
        idx >= 0 && idx < work_list.len(),
        avoid_set.to_set().subset_of(work_list.to_set())
{
    !avoid_set.contains(work_list[idx])
}

proof fn lemma_exists_non_avoided<T>(work_list: Seq<T>, avoid_set: Seq<T>)
    requires
        work_list.len() > 0,
        avoid_set.to_set().subset_of(work_list.to_set()),
        avoid_set.to_set() != work_list.to_set()
    ensures
        exists|i: int| 0 <= i < work_list.len() && index_of_non_avoided(work_list, avoid_set, i)
{
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
    let m_len = m_work_list.len() as int;
    proof {
        lemma_exists_non_avoided(m_work_list@, avoid_set@);
    }
    let mut idx: int = 0;
    proof {
        idx = choose|i: int| 0 <= i < m_len && index_of_non_avoided(m_work_list@, avoid_set@, i);
    }
    let mut found = false;
    let mut count: int = 0;
    let mut idx_usize: usize = idx as usize;
    
    while count < m_len && !found
        invariant
            0 <= count <= m_len,
            exists|i: int| 0 <= i < m_len && index_of_non_avoided(m_work_list@, avoid_set@, i),
            0 <= idx < m_len,
            idx_usize as int == idx,
            count == (if found { m_len } else { count })
        decreases m_len - count
    {
        if !avoid_set.contains(&m_work_list[idx_usize]) {
            found = true;
        } else {
            idx = (idx + 1) % m_len;
            idx_usize = idx as usize;
            count = count + 1;
        }
    }
    
    assert(found) by {
        if !found {
            assert(forall|i: int| 0 <= i < m_len ==> avoid_set@.contains(m_work_list@[i]));
            assert(avoid_set@.to_set() == m_work_list@.to_set());
            assert(false);
        }
    };
    
    m_work_list[idx_usize].clone()
}
// </vc-code>

fn main() {
}

}