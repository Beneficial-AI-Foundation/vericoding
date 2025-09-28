// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3 && s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
}

spec fn valid_abbreviation(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() >= 3 &&
    s.len() >= 3 &&
    result[0] == s[0] &&
    result[result.len() - 1] == s[s.len() - 1] &&
    result == seq![s[0]].add(int_to_string(s.len() - 2)).add(seq![s[s.len() - 1]])
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases if n >= 0 { n } else { -n }
{
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'].add(int_to_string_helper(-n))
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        Seq::new(0 as nat, |_i: int| ' ')
    } else {
        int_to_string_helper(n / 10).add(seq![(('0' as int) + (n % 10)) as char])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause to fix recursion termination */
fn exec_int_to_string_helper(n: u64) -> (result: Vec<char>)
    decreases n
    ensures
        result@ == int_to_string_helper(n as int),
{
    if n == 0 {
        Vec::new()
    } else {
        let rest = exec_int_to_string_helper(n / 10);
        let digit = (n % 10) as u8;
        let char_digit = (digit + ('0' as u8)) as char;
        let mut res = rest;
        res.push(char_digit);
        res
    }
}

/* helper modified by LLM (iteration 2): changed parameter type from int to u64 to avoid ghost type usage */
fn exec_int_to_string(n: u64) -> (result: Vec<char>)
    ensures
        result@ == int_to_string(n as int),
{
    if n == 0 {
        vec!['0']
    } else {
        exec_int_to_string_helper(n)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_abbreviation(s@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): moved function signature into code section to fix missing body error */
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_abbreviation(s@, result@)
{
    let first_char = s[0];
    let last_char = s[s.len() - 1];
    let n_usize = s.len() - 2;
    let n_u64 = n_usize as u64;
    let n_string = exec_int_to_string(n_u64);
    let mut result = Vec::new();
    result.push(first_char);
    for c in n_string {
        result.push(c);
    }
    result.push(last_char);
    result
}
// </vc-code>


}

fn main() {}