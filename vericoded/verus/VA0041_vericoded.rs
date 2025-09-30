// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn contains_lowercase(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && 'a' <= s[i] && s[i] <= 'z'
}

spec fn contains_uppercase(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && 'A' <= s[i] && s[i] <= 'Z'
}

spec fn contains_digit(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && '0' <= s[i] && s[i] <= '9'
}

spec fn is_valid_password(s: Seq<char>) -> bool {
    s.len() >= 5 && contains_lowercase(s) && contains_uppercase(s) && contains_digit(s)
}

spec fn trim_newline(s: Seq<char>) -> Seq<char> {
    if s.len() > 0 && s[s.len() as int - 1] == '\n' { 
        s.subrange(0, s.len() as int - 1) 
    } else { 
        s 
    }
}

spec fn strip_whitespace(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s
    } else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' {
        strip_whitespace(s.subrange(1, s.len() as int))
    } else if s[s.len() as int - 1] == ' ' || s[s.len() as int - 1] == '\t' || s[s.len() as int - 1] == '\n' || s[s.len() as int - 1] == '\r' {
        strip_whitespace(s.subrange(0, s.len() as int - 1))
    } else { 
        s 
    }
}
// </vc-preamble>

// <vc-helpers>
fn is_lowercase(c: char) -> (result: bool)
    ensures result == ('a' <= c && c <= 'z')
{
    'a' <= c && c <= 'z'
}

fn is_uppercase(c: char) -> (result: bool)
    ensures result == ('A' <= c && c <= 'Z')
{
    'A' <= c && c <= 'Z'
}

fn is_digit(c: char) -> (result: bool)
    ensures result == ('0' <= c && c <= '9')
{
    '0' <= c && c <= '9'
}

fn check_contains_lowercase(v: &Vec<char>) -> (result: bool)
    ensures result == contains_lowercase(v@)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> !('a' <= v@[j] && v@[j] <= 'z'),
        decreases v.len() - i
    {
        if is_lowercase(v[i]) {
            return true;
        }
        i += 1;
    }
    false
}

fn check_contains_uppercase(v: &Vec<char>) -> (result: bool)
    ensures result == contains_uppercase(v@)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> !('A' <= v@[j] && v@[j] <= 'Z'),
        decreases v.len() - i
    {
        if is_uppercase(v[i]) {
            return true;
        }
        i += 1;
    }
    false
}

fn check_contains_digit(v: &Vec<char>) -> (result: bool)
    ensures result == contains_digit(v@)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> !('0' <= v@[j] && v@[j] <= '9'),
        decreases v.len() - i
    {
        if is_digit(v[i]) {
            return true;
        }
        i += 1;
    }
    false
}

fn trim_newline_impl(input: &Vec<char>) -> (result: Vec<char>)
    ensures result@ == trim_newline(input@)
{
    if input.len() > 0 && input[input.len() - 1] == '\n' {
        let mut result = Vec::new();
        let mut i = 0;
        while i < input.len() - 1
            invariant
                0 <= i <= input.len() - 1,
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == input@[j],
            decreases input.len() - 1 - i
        {
            result.push(input[i]);
            i += 1;
        }
        result
    } else {
        input.clone()
    }
}

/* helper modified by LLM (iteration 4): added sequence equality assertion in proof block to establish postcondition */
fn strip_whitespace_impl(input: &Vec<char>) -> (result: Vec<char>)
    ensures result@ == strip_whitespace(input@)
    decreases input.len()
{
    if input.len() == 0 {
        input.clone()
    } else if input[0] == ' ' || input[0] == '\t' || input[0] == '\n' || input[0] == '\r' {
        let mut sub = Vec::new();
        let mut i = 1;
        while i < input.len()
            invariant
                1 <= i <= input.len(),
                sub@.len() == i - 1,
                forall|j: int| 1 <= j < i ==> sub@[j-1] == input@[j],
                sub@ == input@.subrange(1, i as int),
            decreases input.len() - i
        {
            sub.push(input[i]);
            i += 1;
        }
        proof {
            assert(sub@ == input@.subrange(1, input@.len() as int));
        }
        strip_whitespace_impl(&sub)
    } else if input[input.len() - 1] == ' ' || input[input.len() - 1] == '\t' || input[input.len() - 1] == '\n' || input[input.len() - 1] == '\r' {
        let mut sub = Vec::new();
        let mut i = 0;
        while i < input.len() - 1
            invariant
                0 <= i <= input.len() - 1,
                sub@.len() == i,
                forall|j: int| 0 <= j < i ==> sub@[j] == input@[j],
                sub@ == input@.subrange(0, i as int),
            decreases input.len() - 1 - i
        {
            sub.push(input[i]);
            i += 1;
        }
        proof {
            assert(sub@ == input@.subrange(0, input@.len() as int - 1));
        }
        strip_whitespace_impl(&sub)
    } else {
        input.clone()
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires input@.len() > 0
    ensures ({
        let processed_input = trim_newline(input@);
        let stripped = strip_whitespace(processed_input);
        if is_valid_password(stripped) {
            output@ == seq!['C', 'o', 'r', 'r', 'e', 'c', 't', '\n']
        } else {
            output@ == seq!['T', 'o', 'o', ' ', 'w', 'e', 'a', 'k', '\n']
        }
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): ensuring is_valid_password check matches spec definition */
    let trimmed = trim_newline_impl(&input);
    let stripped = strip_whitespace_impl(&trimmed);
    
    let has_lowercase = check_contains_lowercase(&stripped);
    let has_uppercase = check_contains_uppercase(&stripped);
    let has_digit = check_contains_digit(&stripped);
    
    if stripped.len() >= 5 && has_lowercase && has_uppercase && has_digit {
        proof {
            assert(is_valid_password(stripped@));
        }
        vec!['C', 'o', 'r', 'r', 'e', 'c', 't', '\n']
    } else {
        proof {
            assert(!is_valid_password(stripped@));
        }
        vec!['T', 'o', 'o', ' ', 'w', 'e', 'a', 'k', '\n']
    }
}
// </vc-code>


}

fn main() {}