// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(t: Seq<char>) -> bool {
    t.len() >= 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helpers, removed unused functions */
spec fn char_at_pos(s: Seq<char>, pos: int) -> char {
    s[pos]
}

proof fn lemma_vec_len_preserves_seq_len(v: Vec<char>)
    ensures v@.len() == v.len()
{
}

fn copy_char_at(source: &Vec<char>, target: &mut Vec<char>, pos: usize)
    requires
        pos < source.len(),
        pos < old(target).len(),
        source.len() == old(target).len(),
        old(target)@.len() == source@.len()
    ensures
        target@.len() == source@.len(),
        target@[pos as int] == source@[pos as int]
{
    target.set(pos, source[pos]);
}
// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires valid_input(t@)
    ensures result@.len() == t@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut result = Vec::with_capacity(t.len());
    let mut i = 0;
    
    while i < t.len()
        invariant
            i <= t.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == t@[j]
        decreases t.len() - i
    {
        result.push(t[i]);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}