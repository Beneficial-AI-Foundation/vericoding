// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_parsed_input(parts: Seq<Seq<char>>) -> bool {
    parts.len() == 3 && parts[0].len() > 0 && parts[1].len() > 0 && parts[2].len() > 0
}

spec fn is_word_chain(a: Seq<char>, b: Seq<char>, c: Seq<char>) -> bool {
    a.len() > 0 && b.len() > 0 && c.len() > 0 &&
    a[a.len() - 1] == b[0] && b[b.len() - 1] == c[0]
}

spec fn split_on_spaces(s: Seq<char>) -> Seq<Seq<char>>;

spec fn expected_result(input: Seq<char>) -> Seq<char> {
    let stripped = if input.len() > 0 && input[input.len() - 1] == '\n' {
        input.subrange(0, input.len() - 1)
    } else {
        input
    };
    let parts = split_on_spaces(stripped);
    if valid_parsed_input(parts) {
        if is_word_chain(parts[0], parts[1], parts[2]) {
            seq!['Y', 'E', 'S', '\n']
        } else {
            seq!['N', 'O', '\n']
        }
    } else {
        seq![]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate function declaration and marked uninterp */
uninterp spec fn split_on_spaces(s: Seq<char>) -> Seq<Seq<char>>;

fn strip_newline(input: Vec<char>) -> (result: Vec<char>)
    requires input@.len() > 0
    ensures result@ == (if input@[input@.len() - 1] == '\n' {
        input@.subrange(0, input@.len() - 1 as int)
    } else {
        input@
    })
{
    if input.len() > 0 && input[input.len() - 1] == '\n' {
        let mut result = Vec::new();
        let mut i = 0;
        while i < input.len() - 1
            invariant
                i <= input.len() - 1,
                result@.len() == i,
                result@ == input@.subrange(0, i as int),
        {
            result.push(input[i]);
            i += 1;
        }
        result
    } else {
        input
    }
}

fn split_spaces(s: Vec<char>) -> (result: Vec<Vec<char>>)
    requires s@.len() > 0
    ensures result@.len() <= 3
{
    let mut parts = Vec::new();
    let mut current_word = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            parts.len() <= 3,
    {
        if s[i] == ' ' {
            if current_word.len() > 0 {
                parts.push(current_word);
                current_word = Vec::new();
            }
        } else {
            current_word.push(s[i]);
        }
        i += 1;
    }
    
    if current_word.len() > 0 {
        parts.push(current_word);
    }
    
    parts
}

fn check_word_chain(a: &Vec<char>, b: &Vec<char>, c: &Vec<char>) -> (result: bool)
    requires
        a@.len() > 0,
        b@.len() > 0,
        c@.len() > 0,
    ensures result == is_word_chain(a@, b@, c@)
{
    a[a.len() - 1] == b[0] && b[b.len() - 1] == c[0]
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@ == expected_result(input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error */
{
    let stripped = strip_newline(input);
    let parts = split_spaces(stripped);
    
    if parts.len() == 3 && parts[0].len() > 0 && parts[1].len() > 0 && parts[2].len() > 0 {
        if check_word_chain(&parts[0], &parts[1], &parts[2]) {
            vec!['Y', 'E', 'S', '\n']
        } else {
            vec!['N', 'O', '\n']
        }
    } else {
        Vec::new()
    }
}
// </vc-code>


}

fn main() {}