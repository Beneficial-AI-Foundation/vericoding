// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn count_as(s: Seq<char>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else if s[0] == 'a' {
            1 + count_as(s.subrange(1, s.len() as int))
        } else {
            count_as(s.subrange(1, s.len() as int))
        }
    }
    
    spec fn remove_as(s: Seq<char>) -> Seq<char>
        decreases s.len()
    {
        if s.len() == 0 {
            seq![]
        } else if s[0] == 'a' {
            remove_as(s.subrange(1, s.len() as int))
        } else {
            seq![s[0]].add(remove_as(s.subrange(1, s.len() as int)))
        }
    }
// </vc-preamble>

// <vc-helpers>

    proof fn lemma_count_as_lemma(s: Seq<char>, c: char)
        ensures
            count_as(s.push(c)) == count_as(s) + if c == 'a' { 1int } else { 0int }
        decreases s.len()
    {
        lemma_helper(s, Seq::empty())
    }

    proof fn lemma_helper(prefix: Seq<char>, suffix: Seq<char>)
        ensures forall |c: char|
            count_as(prefix.push(c).add(suffix)) == count_as(prefix) + if c == 'a' { 1int } else { 0int } + count_as(suffix)
        decreases prefix.len()
    {
        if prefix.len() == 0 {
            assert forall |c: char| count_as(seq![c].add(suffix)) == (if c == 'a' { 1int } else { 0int }) + count_as(suffix) by {
                lemma_count_as_empty_suffix(c, suffix);
            };
        } else {
            let first = prefix[0];
            let rest = prefix.subrange(1, prefix.len() as int);
            assert forall |c: char| count_as(prefix.push(c).add(suffix)) == count_as(prefix) + if c == 'a' { 1int } else { 0int } + count_as(suffix) by {
                lemma_helper(rest, seq![first].add(suffix));
            };
        }
    }

    proof fn lemma_count_as_empty_suffix(c: char, suffix: Seq<char>)
        ensures count_as(seq![c].add(suffix)) == (if c == 'a' { 1int } else { 0int }) + count_as(suffix)
    {
        if c == 'a' {
            assert(count_as(seq!['a'].add(suffix)) == 1int + count_as(suffix));
        } else {
            assert(count_as(seq![c].add(suffix)) == count_as(suffix));
        }
    }

// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires t@.len() >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clause to while loop */
    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    
    while i < t.len()
        invariant
            i <= t@.len(),
            result_vec@ == remove_as(t@.subrange(0, i as int))
        decreases t.len() - i
    {
        if t[i] == 'a' {
            // Skip 'a' characters
        } else {
            result_vec.push(t[i]);
        }
        i = i + 1;
    }
    
    result_vec
}
// </vc-code>


}

fn main() {}