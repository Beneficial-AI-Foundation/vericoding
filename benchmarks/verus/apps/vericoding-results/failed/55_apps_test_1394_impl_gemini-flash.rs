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
/* helper modified by LLM (iteration 5): Fix compiler error. `lemma auto fn` should be `lemma fn`*/
lemma fn remove_as_properties(s: Seq<char>)
    ensures
        remove_as(s).len() == s.len() - count_as(s),
        forall|i: int| #![auto] 0 <= i < remove_as(s).len() ==> remove_as(s)[i] != 'a',
    decreases s.len()
{
    if s.len() == 0 {
    } else if s[0] == 'a' {
        remove_as_properties(s.subrange(1, s.len() as int));
    } else {
        remove_as_properties(s.subrange(1, s.len() as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires t@.len() >= 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no change */
{
    let s_t = t@;
    let s_filtered = remove_as(s_t);
    remove_as_properties(s_t);
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    while i < s_filtered.len()
        invariant
            0 <= i <= s_filtered.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s_filtered[j],
    {
        result.push(s_filtered[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}