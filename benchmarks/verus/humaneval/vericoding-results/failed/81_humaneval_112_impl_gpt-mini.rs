// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn filter_chars(s: Seq<char>, c: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else if c.contains(s[0]) {
        filter_chars(s.subrange(1, s.len() as int), c)
    } else {
        seq![s[0]].add(filter_chars(s.subrange(1, s.len() as int), c))
    }
}

spec fn reverse_seq(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove length of reverse_seq equals original */
proof fn reverse_seq_len(s: Seq<char>)
    ensures
        reverse_seq(s).len() == s.len(),
    decreases s.len()
{
    if s.len() == 0 {
        proof {
            assert(reverse_seq(s).len() == 0);
        }
    } else {
        reverse_seq_len(s.subrange(1, s.len() as int));
        proof {
            assert(reverse_seq(s) == reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]]));
            assert(reverse_seq(s).len() == reverse_seq(s.subrange(1, s.len() as int)).len() + 1);
            assert(reverse_seq(s).len() == s.len());
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn reverse_delete(s: Vec<char>, c: Vec<char>) -> (result: (Vec<char>, bool))
    ensures
        result.0@ == filter_chars(s@, c@),
        result.1 == (result.0@ == reverse_seq(result.0@)),
        result.0@.len() <= s@.len(),
        forall|i: int| #![auto] 0 <= i < result.0@.len() ==> !c@.contains(result.0@[i]),
        forall|i: int| #![auto] 0 <= i < result.0@.len() ==> s@.contains(result.0@[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build filtered vector and check palindrome property */
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            res@ == filter_chars(s@.subrange(0, i as int), c@),
            i <= s.len(),
        decreases s.len() - i
    {
        let ch = s[i];
        if !c@.contains(ch) {
            res.push(ch);
        }
        i = i + 1;
    }

    let result = (res, res@ == reverse_seq(res@));
    result
}
// </vc-code>


}

fn main() {}