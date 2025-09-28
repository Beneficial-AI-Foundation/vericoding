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

// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires t@.len() >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let ghost init_t = t@;
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < t.len()
        invariant
            0 <= i <= t.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == if init_t[j] == 'a' { 'b' } else { init_t[j] },
        decreases t.len() - i
    {
        if t[i] == 'a' {
            result.push('b');
        } else {
            result.push(t[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}