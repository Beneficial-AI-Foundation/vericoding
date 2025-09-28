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
    let mut idx: usize = 0;
    while idx < m_work_list.len()
        invariant
            idx <= m_work_list.len(),
            forall |j: usize| j < idx ==> avoid_set@.contains(m_work_list@[j]),
    {
        if !avoid_set@.contains(m_work_list@[idx]) {
            break;
        }
        idx = idx + 1;
    }
    let e: T;
    if idx < m_work_list.len() {
        e = m_work_list[idx].clone();
    } else {
        e = m_work_list[0].clone();
    }
    e
}
// </vc-code>

fn main() {
}

}