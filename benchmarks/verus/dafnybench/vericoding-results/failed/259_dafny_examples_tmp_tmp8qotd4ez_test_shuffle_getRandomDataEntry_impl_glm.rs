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
exec fn exec_contains<T: PartialEq + Clone>(s: &Vec<T>, e: &T) -> (b: bool)
    ensures b == exists|i: int| 0 <= i < s@.len() && s@[i] == *e
{
    let mut i = 0;
    let n = s.len();
    while i < n 
        invariant 0 <= i <= n
        invariant forall |j: int| 0 <= j < i ==> s@[j] != *e
    {
        if s[i] == *e {
            return true;
        }
        i += 1;
    }
    false
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
    let mut i = 0;
    let n = m_work_list.len();
    while i < n 
        invariant 0 <= i <= n
        invariant forall |j: int| 0 <= j < i ==> avoid_set@.contains(m_work_list@[j])
    {
        let candidate = m_work_list[i].clone();
        if !exec_contains(avoid_set, &candidate) {
            return candidate;
        }
        i += 1;
    }
    m_work_list[0].clone()
}
// </vc-code>

fn main() {
}

}