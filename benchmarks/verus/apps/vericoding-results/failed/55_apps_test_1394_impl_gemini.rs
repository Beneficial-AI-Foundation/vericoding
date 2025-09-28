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
/* helper modified by LLM (iteration 5): corrected the name of the sequence associativity lemma */
proof fn lemma_remove_as_distributive(s1: Seq<char>, s2: Seq<char>)
    ensures
        remove_as(s1.add(s2)) == remove_as(s1).add(remove_as(s2)),
    decreases s1.len()
{
    if s1.len() > 0 {
        let h = s1[0];
        let s1_tail = s1.subrange(1, s1.len() as int);
        lemma_remove_as_distributive(s1_tail, s2);

        if h != 'a' {
            lemma_seq_add_associative(seq![h], remove_as(s1_tail), remove_as(s2));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires t@.len() >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added lemma calls to strengthen the loop invariant proof */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < t.len()
        invariant
            i <= t.len(),
            result@ == remove_as(t@.subrange(0, i as int)),
        decreases t.len() - i
    {
        proof {
            lemma_subrange_append(t@, i as int);
            lemma_remove_as_distributive(t@.subrange(0, i as int), seq![t@[i as int]]);
        }

        let c = t[i];
        if c != 'a' {
            result.push(c);
        }
        i = i + 1;
    }
    result
}

// </vc-code>


}

fn main() {}