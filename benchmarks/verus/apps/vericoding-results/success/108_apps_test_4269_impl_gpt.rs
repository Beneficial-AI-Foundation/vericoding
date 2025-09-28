// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_hard_to_enter(s: Seq<char>) -> bool
    recommends s.len() == 4
{
    s[0] == s[1] || s[1] == s[2] || s[2] == s[3]
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_is_hard_to_enter_equiv(v: &Vec<char>)
    requires
        v@.len() == 4,
    ensures
        is_hard_to_enter(v@) == (v[0] == v[1] || v[1] == v[2] || v[2] == v[3]),
{
    assert(v.len() == v@.len());
    assert(v.len() == 4);
    assert(0 < v.len());
    assert(1 < v.len());
    assert(2 < v.len());
    assert(3 < v.len());
    assert(v@[0] == v[0]);
    assert(v@[1] == v[1]);
    assert(v@[2] == v[2]);
    assert(v@[3] == v[3]);
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires s@.len() == 4
    ensures 
        result@.len() > 0,
        (result@ == seq!['B', 'a', 'd'] <==> is_hard_to_enter(s@)),
        (result@ == seq!['G', 'o', 'o', 'd'] <==> !is_hard_to_enter(s@))
// </vc-spec>
// <vc-code>
{
    assert(s.len() == s@.len());
    assert(s.len() == 4);

    let b = s[0] == s[1] || s[1] == s[2] || s[2] == s[3];
    proof {
        lemma_is_hard_to_enter_equiv(&s);
        assert(b == is_hard_to_enter(s@));
    }

    let mut result: Vec<char> = Vec::new();
    if b {
        result.push('B');
        result.push('a');
        result.push('d');
        assert(result@ == seq!['B', 'a', 'd']);
    } else {
        result.push('G');
        result.push('o');
        result.push('o');
        result.push('d');
        assert(result@ == seq!['G', 'o', 'o', 'd']);
    }
    result
}
// </vc-code>


}

fn main() {}