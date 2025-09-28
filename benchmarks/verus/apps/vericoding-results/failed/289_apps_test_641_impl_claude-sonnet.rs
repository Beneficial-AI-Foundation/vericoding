// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_on_space(s: Seq<char>) -> Seq<Seq<char>>;

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    ({
        let trimmed = if input.len() > 0 && input[input.len() as int - 1] == '\n' { input.subrange(0, input.len() as int - 1) } else { input };
        let parts = split_on_space(trimmed);
        parts.len() >= 1
    })
}

spec fn get_expected_result(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    let trimmed = if input.len() > 0 && input[input.len() as int - 1] == '\n' { input.subrange(0, input.len() as int - 1) } else { input };
    let parts = split_on_space(trimmed);
    if parts[parts.len() as int - 1] == seq!['m', 'o', 'n', 't', 'h'] {
        if parts[0] == seq!['3', '1'] { seq!['7', '\n'] }
        else if parts[0] == seq!['3', '0'] { seq!['1', '1', '\n'] }
        else { seq!['1', '2', '\n'] }
    } else {
        if parts[0] == seq!['5'] || parts[0] == seq!['6'] { seq!['5', '3', '\n'] }
        else { seq!['5', '2', '\n'] }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove duplicate function definition and fix compilation errors */
uninterp spec fn split_on_space(s: Seq<char>) -> Seq<Seq<char>>;

fn char_seq_to_string(s: Seq<char>) -> (result: String)
    ensures result@ == s
{
    let mut vec = Vec::new();
    let mut i = 0usize;
    while i < s.len()
        invariant
            i <= s.len(),
            vec@@ == s.subrange(0, i as int)
    {
        vec.push(s[i as int]);
        i += 1;
    }
    vec.into_iter().collect()
}

fn split_string_on_space(s: &str) -> (result: Vec<String>)
    ensures
        result@.len() >= 1,
        result@@@ == split_on_space(s@)
{
    s.split(' ').map(|x| x.to_string()).collect()
}

fn trim_newline(s: &str) -> (result: String)
    ensures
        result@ == (if s@.len() > 0 && s@[s@.len() as int - 1] == '\n' {
            s@.subrange(0, s@.len() as int - 1)
        } else {
            s@
        })
{
    if s.len() > 0 && s.chars().last() == Some('\n') {
        s[..s.len()-1].to_string()
    } else {
        s.to_string()
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures result@ == get_expected_result(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix indexing with proper usize casting */
    let trimmed = trim_newline(input);
    let parts = split_string_on_space(&trimmed);
    
    let result = if parts[parts.len() - 1] == "month" {
        if parts[0] == "31" {
            "7\n".to_string()
        } else if parts[0] == "30" {
            "11\n".to_string()
        } else {
            "12\n".to_string()
        }
    } else {
        if parts[0] == "5" || parts[0] == "6" {
            "53\n".to_string()
        } else {
            "52\n".to_string()
        }
    };
    
    result
}
// </vc-code>


}

fn main() {}