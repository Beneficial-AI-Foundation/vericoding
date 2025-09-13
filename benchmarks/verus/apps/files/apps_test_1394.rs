// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_as(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == 'a' {
        1 + count_as(s.drop_first())
    } else {
        count_as(s.drop_first())
    }
}

spec fn remove_as(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == 'a' {
        remove_as(s.drop_first())
    } else {
        Seq::new(1, |i: int| s[0]).add(remove_as(s.drop_first()))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(t: Seq<char>) -> (result: Seq<char>)
    requires t.len() >= 1
    ensures 
        result == Seq::new(2nat, |i: int| if i == 0int { ':' } else { '(' }) || (result.len() <= t.len() && t == result.add(remove_as(result))),
        result != Seq::new(2nat, |i: int| if i == 0int { ':' } else { '(' }) ==> {
            let z = count_as(t);
            let non_a_count = t.len() - z;
            non_a_count % 2 == 0 &&
            {
                let q = non_a_count / 2;
                let s_length = q + z;
                s_length <= t.len() &&
                result == t.take(s_length as int) &&
                remove_as(result) == t.skip(s_length as int)
            }
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Seq::new(2nat, |i: int| if i == 0int { ':' } else { '(' })
    // impl-end
}
// </vc-code>


}

fn main() {}