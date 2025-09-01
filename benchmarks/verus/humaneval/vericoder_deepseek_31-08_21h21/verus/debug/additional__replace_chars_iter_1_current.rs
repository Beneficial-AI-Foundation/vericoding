use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn replace_chars_proof(s: Seq<char>, old: char, new: char, result: Vec<char>, i: int)
    requires
        0 <= i && i <= s.len(),
        result.len() == s.len(),
        forall|j: int| 0 <= j && j < i ==> result@[j] == (if s[j] == old { new } else { s[j] }),
    ensures
        forall|j: int| 0 <= j && j < i ==> result@[j] == (if s[j] == old { new } else { s[j] }),
{
}
// </vc-helpers>

// <vc-spec>
fn replace_chars(s: &[char], old: char, new: char) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if s[i] == old { new } else { s[i] }),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(s.len());
    let mut idx: usize = 0;
    
    while idx < s.len()
        invariant
            result.len() == idx,
            forall|i: int| 0 <= i && i < idx ==> result@[i] == (if s[i] == old { new } else { s[i] }),
        decreases s.len() - idx,
    {
        let current_char = s[idx];
        let new_char = if current_char == old { new } else { current_char };
        result.push(new_char);
        proof {
            replace_chars_proof(s@, old, new, result, idx);
        }
        idx = idx + 1;
    }
    
    proof {
        assert(result.len() == s.len());
    }
    
    result
}
// </vc-code>

fn main() {}
}