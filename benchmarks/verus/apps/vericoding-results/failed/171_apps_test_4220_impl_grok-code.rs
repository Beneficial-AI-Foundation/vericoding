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

/* helper modified by LLM (iteration 4): executable newline finder */
fn find_newline_exec(s: &Vec<char>, start: usize) -> (r: usize)
    requires start <= s.len()
    ensures r == find_newline(s@, start as nat) as usize
{
    let mut i = start;
    while i < s.len()
        invariant start <= i <= s.len()
        decreases s.len() - i
    {
        if s[i] == '
' {
            return i;
        }
        i += 1;
    }
    return i;
}

/* helper modified by LLM (iteration 5): executable string to int conversion with named return */
fn string_to_int_exec(s: &Vec<char>) -> (result: u32)
    requires is_valid_positive_integer(s@)
    ensures (result as int) == string_to_int(s@)
{
    let mut acc: u32 = 0;
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len()
        decreases s.len() - i
    {
        let digit = (s[i] as u32) - ('0' as u32);
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

/* code modified by LLM (iteration 5): implemented the solve function logic */
{
    let newline_pos = find_newline_exec(&stdin_input, 0);
    let k_slice = &stdin_input[0..newline_pos];
    let k_vec = k_slice.to_vec();
    let k = string_to_int_exec(&k_vec) as usize;
    let rest_start = newline_pos + 1;
    let rest_slice = if rest_start > stdin_input.len() { &[] } else { &stdin_input[rest_start..] };
    let mut s_vec: Vec<char> = rest_slice.to_vec();
    proof {
        assert(valid_input(stdin_input@));
    }
    if s_vec.len() > 0 && s_vec[s_vec.len() - 1] == '
' {
        s_vec.pop();
    }
    if s_vec.len() <= k {
        let mut result = s_vec;
        result.push('
');
        result
    } else {
        let mut result = s_vec[0..k].to_vec();
        result.push('.');
        result.push('.');
        result.push('.');
        result.push('
');
        result
    }
}

// </vc-code>


}

fn main() {}