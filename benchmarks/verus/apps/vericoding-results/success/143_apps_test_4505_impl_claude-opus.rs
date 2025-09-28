// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    (s.len() == 3 || (s.len() == 4 && s[3] == '\n')) &&
    forall|i: int| 0 <= i < (if s.len() == 4 { 3 } else { s.len() as int }) ==> 
        (s[i] == 'a' || s[i] == 'b' || s[i] == 'c')
}

spec fn get_input_chars(s: Seq<char>) -> Seq<char> {
    if s.len() == 4 { s.subrange(0, 3) } else { s }
}

spec fn is_permutation_of_abc(input_chars: Seq<char>) -> bool {
    input_chars.len() == 3 &&
    (forall|i: int| 0 <= i < input_chars.len() ==> 
        (input_chars[i] == 'a' || input_chars[i] == 'b' || input_chars[i] == 'c')) &&
    input_chars[0] != input_chars[1] && 
    input_chars[1] != input_chars[2] && 
    input_chars[0] != input_chars[2]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        s@.len() >= 3,
        valid_input(s@),
    ensures 
        result@ == seq!['Y', 'e', 's', '\n'] || result@ == seq!['N', 'o', '\n'],
        result@ == seq!['Y', 'e', 's', '\n'] <==> is_permutation_of_abc(get_input_chars(s@)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed array indexing bounds and invariant */
    let input_chars = if s.len() == 4 {
        vec![s[0], s[1], s[2]]
    } else {
        vec![s[0], s[1], s[2]]
    };
    
    let mut is_perm = true;
    
    // Check all characters are a, b, or c
    let mut i = 0;
    while i < 3
        invariant
            0 <= i <= 3,
            input_chars@.len() == 3,
            is_perm == (forall|j: int| 0 <= j < i ==> 
                0 <= j < input_chars@.len() &&
                (input_chars@[j] == 'a' || input_chars@[j] == 'b' || input_chars@[j] == 'c')),
        decreases 3 - i
    {
        if !(input_chars[i] == 'a' || input_chars[i] == 'b' || input_chars[i] == 'c') {
            is_perm = false;
        }
        i = i + 1;
    }
    
    // Check all different
    if is_perm {
        if input_chars[0] == input_chars[1] || 
           input_chars[1] == input_chars[2] || 
           input_chars[0] == input_chars[2] {
            is_perm = false;
        }
    }
    
    if is_perm {
        vec!['Y', 'e', 's', '\n']
    } else {
        vec!['N', 'o', '\n']
    }
}
// </vc-code>


}

fn main() {}