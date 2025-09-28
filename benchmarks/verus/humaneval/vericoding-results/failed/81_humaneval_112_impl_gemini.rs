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
/* helper modified by LLM (iteration 2): corrected base case for recursion in lemma */
proof fn lemma_reverse_seq_len(s: Seq<char>)
    ensures reverse_seq(s).len() == s.len()
    decreases s.len()
{
    if s.len() > 0 {
        lemma_reverse_seq_len(s.subrange(1, s.len() as int));
    }
}

/* helper modified by LLM (iteration 2): corrected base case for recursion in lemma */
proof fn lemma_reverse_seq_index(s: Seq<char>, i: int)
    requires 0 <= i < s.len()
    ensures reverse_seq(s)[i] == s[s.len() - 1 - i]
    decreases s.len()
{
    lemma_reverse_seq_len(s);
    if s.len() > 1 {
        let s_tail = s.subrange(1, s.len() as int);
        if i < s.len() - 1 {
            lemma_reverse_seq_index(s_tail, i);
        }
    }
}

/* helper modified by LLM (iteration 4): removed problematic invariant that was causing compilation error */
fn reverse_vec(v: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@ == reverse_seq(v@),
{
    let mut reversed_vec = Vec::new();
    let len = v.len();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            reversed_vec@.len() == i as int,
            forall|j: int| 0 <= j < (i as int) ==> reversed_vec@[j] == v@[(len as int) - 1 - j],
        decreases len - i
    {
        reversed_vec.push(v[len - 1 - i]);
        i = i + 1;
    }

    proof {
        lemma_reverse_seq_len(v@);
        assert(reversed_vec@.len() == reverse_seq(v@).len());
        assert forall|j: int| 0 <= j < (len as int) implies reversed_vec@[j] == reverse_seq(v@)[j] by {
            lemma_reverse_seq_index(v@, j);
        }
        assert(reversed_vec@ == reverse_seq(v@));
    }

    reversed_vec
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
/* code modified by LLM (iteration 4): fixed old() syntax in loop invariants */
{
    let mut filtered_vec = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            s@ == old(s)@,
            c@ == old(c)@,
            filtered_vec@ == filter_chars(s@.subrange(0, i as int), c@),
        decreases s.len() - i
    {
        if !c.contains(&s[i]) {
            filtered_vec.push(s[i]);
        }
        i += 1;
    }

    let reversed_filtered_vec = reverse_vec(&filtered_vec);
    let is_pal = filtered_vec == reversed_filtered_vec;

    (filtered_vec, is_pal)
}
// </vc-code>


}

fn main() {}