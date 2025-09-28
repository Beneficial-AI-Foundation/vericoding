// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
fn vec_contains<T: PartialEq>(v: &Vec<T>, e: &T) -> (res: bool)
    ensures
        res == v@.contains(*e),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] != *e,
        decreases v.len() - i,
    {
        if v[i] == *e {
            return true;
        }
        i = i + 1;
    }
    false
}

/* helper modified by LLM (iteration 5): fixed call to a non-existent lemma by using the correct one from vstd::set_lib */
proof fn forall_to_contains<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        forall|k: int| 0 <= k < s1.len() ==> s2.contains(s1@[k]),
    ensures
        s1.to_set().subset_of(s2.to_set()),
{
    vstd::set_lib::lemma_seq_to_set_is_subset(s1, s2);
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
/* code modified by LLM (iteration 5): added explicit lemma call for set equality to make proof more robust */
{
    let mut i: usize = 0;
    while i < m_work_list.len()
        invariant
            0 <= i <= m_work_list.len(),
            forall|k: int| 0 <= k < i ==> avoid_set@.contains(m_work_list@[k]),
        decreases m_work_list.len() - i,
    {
        let e = &m_work_list[i];
        if !vec_contains(avoid_set, e) {
            return e.clone();
        }
        i = i + 1;
    }

    proof {
        forall_to_contains(m_work_list@, avoid_set@);
        if set_of_seq(avoid_set@).subset_of(set_of_seq(m_work_list@)) {
            // After the loop, we know m_work_list is a subset of avoid_set (in terms of elements).
            // If we also assume the reverse, the sets are equal.
            vstd::set_lib::lemma_set_ext_equal(m_work_list@.to_set(), avoid_set@.to_set());
            assert(set_of_seq(m_work_list@) == set_of_seq(avoid_set@));
        }
    }
    
    m_work_list[0].clone()
}
// </vc-code>

}
fn main() {}