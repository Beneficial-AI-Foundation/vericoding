// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(s: Seq<int>, x: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == x { 1int } else { 0int }) + count_occurrences(s.subrange(1, s.len() as int), x)
    }
}

spec fn count_pairs(s: Seq<int>) -> int
{
    let positive_sessions = filter_positive(s);
    count_pairs_helper(positive_sessions)
}

spec fn filter_positive(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] > 0 {
        seq![s[0]].add(filter_positive(s.subrange(1, s.len() as int)))
    } else {
        filter_positive(s.subrange(1, s.len() as int))
    }
}

spec fn remove_all_occurrences(s: Seq<int>, x: int) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == x {
        remove_all_occurrences(s.subrange(1, s.len() as int), x)
    } else {
        seq![s[0]].add(remove_all_occurrences(s.subrange(1, s.len() as int), x))
    }
}

spec fn count_pairs_helper(s: Seq<int>) -> int
    decreases s.len()
    when s.len() > 1 ==> remove_all_occurrences(s, s[0]).len() < s.len()
{
    if s.len() <= 1 {
        0
    } else {
        let count = count_occurrences(s, s[0]);
        let remaining = remove_all_occurrences(s, s[0]);
        (if count == 2 { 1int } else { 0int }) + count_pairs_helper(remaining)
    }
}

spec fn exists_index(s: Seq<int>, x: int) -> bool
{
    exists|i: int| 0 <= i < s.len() && s[i] == x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, sessions: Vec<i8>) -> (result: i8)
    requires 
        n >= 1,
        sessions.len() == n as nat,
        forall|i: int| 0 <= i < sessions.len() ==> sessions[i] as int >= 0,
    ensures 
        result == -1 || result >= 0,
        result == -1 ==> (exists|id: int| id > 0 && #[trigger] count_occurrences(sessions@.map_values(|x: i8| x as int), id) > 2),
        result >= 0 ==> forall|id: int| id > 0 ==> count_occurrences(sessions@.map_values(|x: i8| x as int), id) <= 2,
        result >= 0 ==> result as int == count_pairs(sessions@.map_values(|x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}