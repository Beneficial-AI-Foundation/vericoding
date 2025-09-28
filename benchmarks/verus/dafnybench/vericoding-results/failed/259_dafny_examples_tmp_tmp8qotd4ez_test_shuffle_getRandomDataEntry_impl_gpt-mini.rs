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
fn find_random_data_entry_helper<T: PartialEq + Clone>(m_work_list: &Vec<T>, avoid_set: &Vec<T>, i: nat) -> (e: T)
    requires m_work_list.len() > 0
    decreases(m_work_list@.len() - i)
    ensures 
        set_of_seq(avoid_set@).subset_of(set_of_seq(m_work_list@)) && 
        set_of_seq(avoid_set@) != set_of_seq(m_work_list@) ==> !avoid_set@.contains(e),
        (forall |x: T| avoid_set@.contains(x) ==> m_work_list@.contains(x)) && 
        avoid_set@ != m_work_list@ ==> m_work_list@.contains(e)
{
    if i < m_work_list@.len() {
        if !avoid_set@.contains(m_work_list@[i]) {
            m_work_list[i as usize].clone()
        } else {
            let res = find_random_data_entry_helper(m_work_list, avoid_set, i + 1);
            res
        }
    } else {
        m_work_list[0].clone()
    }
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
    find_random_data_entry_helper(m_work_list, avoid_set, 0)
}
// </vc-code>

fn main() {
}

}