// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    exists|i: int, j: int| 0 <= i < j < input.len() && input[i] == ' ' && input[j] == ' ' &&
    ({
        let parts = split_string_spec(input);
        parts.len() >= 3 && 
        is_valid_integer(parts[0]) && is_valid_integer(parts[1]) && is_valid_integer(parts[2]) &&
        ({
            let a = string_to_int_spec(parts[0]);
            let b = string_to_int_spec(parts[1]);
            let c = string_to_int_spec(parts[2]);
            1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
        })
    })
}

spec fn compute_drinks(a: int, b: int, c: int) -> int {
    if b / a < c { b / a } else { c }
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && s[i] <= '9'
}

spec fn string_to_int_spec(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 1 { 
        s[0] as int - '0' as int
    } else if s.len() > 1 { 
        string_to_int_spec(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int)
    } else {
        0
    }
}

spec fn split_string_spec(s: Seq<char>) -> Seq<Seq<char>> {
    if s.len() == 0 { 
        seq![] 
    } else {
        split_helper(s, 0, seq![])
    }
}

spec fn split_helper(s: Seq<char>, index: int, current: Seq<char>) -> Seq<Seq<char>>
    decreases s.len() - index
{
    if index >= s.len() {
        if current.len() > 0 { seq![current] } else { seq![] }
    } else if s[index] == ' ' || s[index] == '\n' || s[index] == '\t' {
        if current.len() > 0 { 
            seq![current] + split_helper(s, index + 1, seq![])
        } else { 
            split_helper(s, index + 1, seq![])
        }
    } else {
        split_helper(s, index + 1, current.push(s[index]))
    }
}

spec fn int_to_string_spec(n: int) -> Seq<char>
    decreases n
{
    if n == 0 { 
        seq!['0'] 
    } else if n < 10 && n > 0 { 
        seq![('0' as int + n) as char]
    } else if n > 0 { 
        int_to_string_spec(n / 10) + seq![('0' as int + (n % 10)) as char]
    } else {
        seq!['0']
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed s.map closure signature */
spec fn to_seq_of_seq(s: Seq<Vec<char>>) -> Seq<Seq<char>> {
    s.map(|_i: int, v: Vec<char>| v@)
}

/* helper modified by LLM (iteration 2): changed from a spec function to an exec function */
fn is_whitespace(c: char) -> bool {
    c == ' ' || c == '\n' || c == '\t'
}

/* helper modified by LLM (iteration 3): fixed type mismatches in specs by using to_seq_of_seq */
fn split_string(s: &Vec<char>) -> (result: Vec<Vec<char>>)
    ensures
        to_seq_of_seq(result@) == split_string_spec(s@),
{
    let mut parts = Vec::<Vec<char>>::new();
    let mut current_part = Vec::<char>::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            split_string_spec(s@) == to_seq_of_seq(parts@) + split_helper(s@, i as int, current_part@),
        decreases s.len() - i
    {
        let c = s[i];
        if is_whitespace(c) {
            if current_part.len() > 0 {
                parts.push(current_part);
                current_part = Vec::new();
            }
        } else {
            current_part.push(c);
        }
        i = i + 1;
    }
    if current_part.len() > 0 {
        parts.push(current_part);
    }
    parts
}

/* helper modified by LLM (iteration 3): fixed spec indexing in proof block */
fn string_to_int(s: &Vec<char>) -> (result: u64)
    requires
        is_valid_integer(s@),
    ensures
        result as int == string_to_int_spec(s@),
{
    let mut num: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_valid_integer(s@),
            num as int == string_to_int_spec(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        proof {
            assert(s@[i as int] >= '0' && s@[i as int] <= '9');
        }
        num = num * 10 + (s[i] as u8 - '0' as u8) as u64;
        i = i + 1;
    }
    num
}

/* helper modified by LLM (iteration 2): changed types from spec 'int' to exec 'u64' to fix compilation issues */
fn int_to_string(n: u64) -> (result: Vec<char>)
    ensures
        result@ == int_to_string_spec(n as int),
    decreases n
{
    if n < 10 {
        let c = ('0' as u8 + n as u8) as char;
        vec![c]
    } else {
        let mut prefix = int_to_string(n / 10);
        let last_digit_char = ('0' as u8 + (n % 10) as u8) as char;
        prefix.push(last_digit_char);
        prefix
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires
        valid_input(input@),
    ensures
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        ({
            let parts = split_string_spec(input@);
            let a = string_to_int_spec(parts[0]);
            let b = string_to_int_spec(parts[1]);
            let c = string_to_int_spec(parts[2]);
            let drinks = compute_drinks(a, b, c);
            result@ == int_to_string_spec(drinks) + seq!['\n']
        }),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): no logical changes, re-attempting verification after fixing helpers */
{
    let parts = split_string(&input);
    let a = string_to_int(&parts[0]);
    let b = string_to_int(&parts[1]);
    let c = string_to_int(&parts[2]);

    let drinks = if b / a < c { b / a } else { c };

    let mut result_vec = int_to_string(drinks);
    result_vec.push('\n');

    result_vec
}
// </vc-code>


}

fn main() {}