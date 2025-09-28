// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 &&
    (exists|i: int| 0 <= i < stdin_input.len() && stdin_input[i] == '\n') &&
    ({
        let newline_pos = find_newline(stdin_input, 0);
        let k_str = stdin_input.subrange(0, newline_pos as int);
        is_valid_positive_integer(k_str)
    }) &&
    ({
        let newline_pos = find_newline(stdin_input, 0);
        let k_str = stdin_input.subrange(0, newline_pos as int);
        let k = string_to_int(k_str);
        1 <= k <= 100
    }) &&
    ({
        let newline_pos = find_newline(stdin_input, 0);
        let rest = stdin_input.subrange(newline_pos as int + 1, stdin_input.len() as int);
        let s = if rest.len() > 0 && rest[rest.len() - 1] == '\n' { rest.subrange(0, rest.len() - 1) } else { rest };
        1 <= s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
    })
}

spec fn extract_k(stdin_input: Seq<char>) -> int
    recommends valid_input(stdin_input)
{
    let newline_pos = find_newline(stdin_input, 0);
    let k_str = stdin_input.subrange(0, newline_pos as int);
    string_to_int(k_str)
}

spec fn extract_s(stdin_input: Seq<char>) -> Seq<char>
    recommends valid_input(stdin_input)
{
    let newline_pos = find_newline(stdin_input, 0);
    let rest = stdin_input.subrange(newline_pos as int + 1, stdin_input.len() as int);
    if rest.len() > 0 && rest[rest.len() - 1] == '\n' { rest.subrange(0, rest.len() - 1) } else { rest }
}

spec fn correct_output(stdin_input: Seq<char>, result: Seq<char>) -> bool
    recommends valid_input(stdin_input)
{
    let k = extract_k(stdin_input);
    let s = extract_s(stdin_input);
    k >= 1 && k <= 100 &&
    s.len() >= 1 && s.len() <= 100 &&
    (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z') &&
    (s.len() <= k ==> result == s.add(seq!['\n'])) &&
    (s.len() > k ==> result == s.subrange(0, k).add(seq!['.', '.', '.']).add(seq!['\n']))
}

spec fn find_newline(s: Seq<char>, start: nat) -> nat
    recommends start <= s.len()
    decreases s.len() - start
{
    if start >= s.len() { 
        s.len() 
    } else if s[start as int] == '\n' { 
        start 
    } else { 
        find_newline(s, start + 1) 
    }
}

spec fn is_valid_positive_integer(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9') && 
    s != seq!['0']
}

spec fn string_to_int(s: Seq<char>) -> int
    recommends is_valid_positive_integer(s)
{
    string_to_int_helper(s, 0, 0)
}

spec fn string_to_int_helper(s: Seq<char>, pos: nat, acc: int) -> int
    recommends
        pos <= s.len(),
        acc >= 0,
        forall|i: int| 0 <= i < pos ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9',
        is_valid_positive_integer(s)
    decreases s.len() - pos
{
    if pos >= s.len() { 
        if acc == 0 { 1 } else { acc }
    } else if s[pos as int] >= '0' && s[pos as int] <= '9' {
        string_to_int_helper(s, pos + 1, acc * 10 + (s[pos as int] as int - '0' as int))
    } else {
        if acc == 0 { 1 } else { acc }
    }
}
// </vc-preamble>

// <vc-helpers>
fn find_newline_exec(s: &Vec<char>, start: usize) -> (pos: usize)
    requires start <= s.len()
    ensures pos == find_newline(s@, start)
    decreases s.len() - start
{
    if start >= s.len() {
        s.len()
    } else if s[start] == '\n' {
        start
    } else {
        find_newline_exec(s, start + 1)
    }
}

/* helper modified by LLM (iteration 4): fixed invariant block syntax by removing curly braces */
fn string_to_int_exec(s: &Vec<char>, start: usize, end: usize) -> (n: int)
    requires
        start <= end,
        end <= s.len(),
        forall|i: int| start <= i < end ==> s[i as usize] >= '0' && s[i as usize] <= '9',
        start < end,
    ensures
        n == string_to_int(s@.subrange(start as int, end as int)),
{
    let mut acc = 0;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            acc >= 0,
            acc == string_to_int_helper(s@.subrange(start as int, end as int), i - start, 0),
        decreases (end - i)
    {
        let digit = s[i] as int - '0' as int;
        acc = acc * 10 + digit;
        i += 1;
    }
    acc
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): updated iteration number */
    let newline_pos = find_newline_exec(&stdin_input, 0);
    let k_str = &stdin_input[0..newline_pos];
    let k = string_to_int_exec(k_str, 0, k_str.len());
    let k_usize = k as usize;

    let rest_start = newline_pos + 1;
    let rest_end = if rest_start < stdin_input.len() && stdin_input[stdin_input.len()-1] == '\n' {
        stdin_input.len() - 1
    } else {
        stdin_input.len()
    };
    let s = &stdin_input[rest_start..rest_end];

    let mut result: Vec<char> = Vec::new();
    if s.len() <= k_usize {
        result.extend(s);
        result.push('\n');
    } else {
        for i in 0..k_usize {
            result.push(s[i]);
        }
        result.push('.');
        result.push('.');
        result.push('.');
        result.push('\n');
    }
    result
}
// </vc-code>


}

fn main() {}