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
fn lemma_avoid_not_equal_work_implies_exists_valid_element<T>(work_list: Seq<T>, avoid_set: Seq<T>)
    requires 
        work_list.len() > 0,
        (forall |x: T| avoid_set.contains(x) ==> work_list.contains(x)),
        avoid_set != work_list
    ensures exists |i: int| 0 <= i < work_list.len() && !avoid_set.contains(work_list[i])
{
    if avoid_set.len() == 0nat {
        assert(!avoid_set.contains(work_list[0]));
    } else {
        assert(work_list.to_set() =~= avoid_set.to_set() ==> false);
        assert(exists |x: T| work_list.contains(x) && !avoid_set.contains(x));
        let x = choose |x: T| work_list.contains(x) && !avoid_set.contains(x);
        let i = choose |i: int| 0 <= i < work_list.len() && work_list[i] == x;
        assert(!avoid_set.contains(work_list[i]));
    }
}

fn find_valid_index<T: PartialEq>(work_list: &Vec<T>, avoid_set: &Vec<T>) -> (idx: usize)
    requires 
        work_list.len() > 0,
        (forall |x: T| avoid_set@.contains(x) ==> work_list@.contains(x)),
        avoid_set@ != work_list@
    ensures 
        idx < work_list.len(),
        !avoid_set@.contains(work_list@[idx as int])
{
    lemma_avoid_not_equal_work_implies_exists_valid_element(work_list@, avoid_set@);
    
    let mut i = 0;
    while i < work_list.len()
        invariant 
            i <= work_list.len(),
            work_list.len() > 0,
            (forall |x: T| avoid_set@.contains(x) ==> work_list@.contains(x)),
            avoid_set@ != work_list@,
            exists |j: int| i as int <= j < work_list.len() && !avoid_set@.contains(work_list@[j])
    {
        proof {
            let ghost_i = i as int;
            if !avoid_set@.contains(work_list@[ghost_i]) {
                return i;
            }
        }
        i += 1;
    }
    unreached()
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
    if set_of_seq(avoid_set@).subset_of(set_of_seq(m_work_list@)) && 
       set_of_seq(avoid_set@) =~= set_of_seq(m_work_list@) == false {
        
        assert((forall |x: T| avoid_set@.contains(x) ==> m_work_list@.contains(x)));
        assert(avoid_set@ != m_work_list@);
        
        let idx = find_valid_index(m_work_list, avoid_set);
        proof {
            let ghost_idx = idx as int;
            assert(!avoid_set@.contains(m_work_list@[ghost_idx]));
        }
        m_work_list[idx].clone()
    } else {
        proof {
            let ghost_len = m_work_list.len() as int;
            let rand_idx = random(0, ghost_len - 1);
            if rand_idx >= 0 && rand_idx < ghost_len {
                m_work_list[rand_idx as usize].clone()
            } else {
                m_work_list[0].clone()
            }
        }
    }
}
// </vc-code>

fn main() {
}

}