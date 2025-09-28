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
proof fn lemma_permutation_check(abc: Seq<char>) 
    requires 
        abc.len() == 3, 
        forall|i: int| 0 <= i < 3 ==> (abc[i] == 'a' || abc[i] == 'b' || abc[i] == 'c') 
    ensures 
        is_permutation_of_abc(abc) == (
            abc[0] != abc[1] && abc[1] != abc[2] && abc[0] != abc[2]
        ) 
{
} 
 
fn check_permutation_of_abc(input_chars: &Vec<char>) -> (result: bool) 
    requires 
        input_chars@.len() == 3, 
        forall|i: int| 0 <= i < 3 ==> (input_chars@[i] == 'a' || input_chars@[i] == 'b' || input_chars@[i] == 'c') 
    ensures 
        result == is_permutation_of_abc(input_chars@) 
{
    proof { 
        lemma_permutation_check(input_chars@); 
    } 
    let a0 = input_chars[0]; 
    let a1 = input_chars[1]; 
    let a2 = input_chars[2]; 
    let result = a0 != a1 && a1 != a2 && a0 != a2;
    result
}
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
    /* code modified by LLM (iteration 3): Replaced Vec::from with manual Vec construction */
    let input_chars = if s.len() == 4 {
        let mut chars = Vec::new();
        chars.push(s[0]);
        chars.push(s[1]);
        chars.push(s[2]);
        chars
    } else {
        s
    };
    
    let is_permutation = check_permutation_of_abc(&input_chars);
    
    if is_permutation {
        let mut result = Vec::new();
        result.push('Y');
        result.push('e');
        result.push('s');
        result.push('\n');
        result
    } else {
        let mut result = Vec::new();
        result.push('N');
        result.push('o');
        result.push('\n');
        result
    }
}
// </vc-code>


}

fn main() {}