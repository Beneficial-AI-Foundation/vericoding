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
fn get_random_index<T>(work_list: &Vec<T>, avoid_set: &Vec<T>) -> (idx: int)
    requires
        work_list.len() > 0,
        set_of_seq(avoid_set@).subset_of(set_of_seq(work_list@)) && set_of_seq(avoid_set@) != set_of_seq(work_list@)
    ensures
        0 <= idx < work_list.len(),
        !avoid_set@.contains(work_list@[idx])
{
    let mut idx: int = 0;
    let current_work_list_len: nat = work_list.len(); // Changed to nat

    while (idx as nat) < work_list.len() && avoid_set@.contains(work_list@[idx])
        invariant
            0 <= idx <= current_work_list_len,
            current_work_list_len == work_list.len(), // Now nat
            forall |k: int| 0 <= k < idx ==> avoid_set@.contains(work_list@[k]),
            set_of_seq(avoid_set@).subset_of(set_of_seq(work_list@.subsequence(idx, current_work_list_len as int))), // Cast back to int for subsequence
            set_of_seq(avoid_set@) != set_of_seq(work_list@.subsequence(idx, current_work_list_len as int)) // Cast back to int for subsequence
        decreases (current_work_list_len - idx)
    {
        idx = idx + 1;
    }
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
    let idx = get_random_index(m_work_list, avoid_set);
    m_work_list[idx as usize].clone()
}
// </vc-code>

fn main() {
}

}