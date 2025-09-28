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
fn string_to_int(s: &Vec<char>) -> (result: u32)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s[i as int] >= '0' && s[i as int] <= '9',
        s.len() <= 10,
    ensures
        result == string_to_int_spec(s@),
{
    let mut n: u32 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            n == string_to_int_spec(s@.subrange(0, i as int)),
            forall|j: int| 0 <= j < s.len() ==> s[j] >= '0' && s[j] <= '9',
    {
        let digit = s[i] as u32 - '0' as u32;
        n = n * 10 + digit;
        i = i + 1;
    }
    n
}

fn split_string(s: &Vec<char>) -> (result: Vec<Vec<char>>)
    ensures
        result@ == split_string_spec(s@),
{
    let mut parts: Vec<Vec<char>> = Vec::new();
    let mut current: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            parts@ + if current@.len() > 0 { seq![current@] } else { seq![] } == split_helper(s@.subrange(0, i as int), 0, seq![]),
    {
        if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' {
            if current.len() > 0 {
                parts.push(current);
                current = Vec::new();
            }
        } else {
            current.push(s[i]);
        }
        i = i + 1;
    }
    
    if current.len() > 0 {
        parts.push(current);
    }
    
    parts
}

fn int_to_string(n: u32) -> (result: Vec<char>)
    requires
        0 <= n <= 100,
    ensures
        result@ == int_to_string_spec(n as int),
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    
    let mut digits: Vec<char> = Vec::new();
    let mut num = n;
    
    while num > 0
        invariant
            0 <= num <= n,
            digits@.len() >= 0,
    {
        let digit = (num % 10) as u8;
        digits.push(('0' as u8 + digit) as char);
        num = num / 10;
    }
    
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = digits.len();
    
    while i > 0
        invariant
            0 <= i <= digits.len(),
    {
        i = i - 1;
        result.push(digits[i]);
    }
    
    result
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
{
    let parts = split_string(&input);
    
    let a = string_to_int(&parts[0]);
    let b = string_to_int(&parts[1]);
    let c = string_to_int(&parts[2]);
    
    let drinks = if b / a < c { b / a } else { c };
    
    let mut result = int_to_string(drinks);
    result.push('\n');
    
    result
}
// </vc-code>


}

fn main() {}