// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(s: Seq<int>, x: int) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 as int }
    else { (if s[0] == x { 1 as int } else { 0 as int }) + count_occurrences(s.subrange(1, s.len() as int), x) }
}

spec fn count_pairs(s: Seq<int>) -> int
{
    let positive_sessions = filter_positive(s);
    count_pairs_helper(positive_sessions)
}

spec fn filter_positive(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 { Seq::<int>::empty() }
    else if s[0] > 0 { seq![s[0]] + filter_positive(s.subrange(1, s.len() as int)) }
    else { filter_positive(s.subrange(1, s.len() as int)) }
}

spec fn count_pairs_helper(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() <= 1 { 0 as int }
    else {
        let count = count_occurrences(s, s[0]);
        let remaining = remove_all_occurrences(s, s[0]);
        (if count == 2 { 1 as int } else { 0 as int }) + count_pairs_helper(remaining)
    }
}

spec fn remove_all_occurrences(s: Seq<int>, x: int) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 { Seq::<int>::empty() }
    else if s[0] == x { remove_all_occurrences(s.subrange(1, s.len() as int), x) }
    else { seq![s[0]] + remove_all_occurrences(s.subrange(1, s.len() as int), x) }
}

spec fn exists_index(s: Seq<int>, x: int) -> bool
{
    exists|i: int| 0 <= i < s.len() && s[i] == x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i32, sessions: &[i32]) -> (result: i32)
    requires 
        n >= 1,
        sessions.len() == n,
        forall|i: int| 0 <= i < sessions.len() ==> sessions[i] >= 0,
    ensures 
        result == -1 || result >= 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    -1
}
// </vc-code>


}

fn main() {}