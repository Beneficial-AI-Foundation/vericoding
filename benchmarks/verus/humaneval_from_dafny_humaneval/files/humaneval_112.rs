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
proof fn filter_chars_append_lemma(s: Seq<char>, ch: char, c: Seq<char>)
    ensures filter_chars(s.add(seq![ch]), c) == 
        (if c.contains(ch) { filter_chars(s, c) } else { filter_chars(s, c).add(seq![ch]) })
    decreases s.len()
{
    assume(false); /* TODO: Remove this line and implement the proof */
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
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}