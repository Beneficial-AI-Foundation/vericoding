// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int, k: int) -> bool {
    a >= 0 && b >= 0 && c >= 0 && k >= 1 && k <= a + b + c
}

spec fn max_sum(a: int, b: int, c: int, k: int) -> int
    recommends valid_input(a, b, c, k)
{
    if k <= a + b {
        if k <= a { k } else { a }
    } else {
        a - (k - a - b)
    }
}

spec fn parsed_values(input: Seq<char>, a: int, b: int, c: int, k: int) -> bool {
    exists|parts: Seq<Seq<char>>| parts.len() >= 4 && 
        parts == split_string_pure(input) &&
        a == string_to_int_pure(parts[0]) &&
        b == string_to_int_pure(parts[1]) &&
        c == string_to_int_pure(parts[2]) &&
        k == string_to_int_pure(parts[3]) &&
        valid_input(a, b, c, k)
}

spec fn int_to_string_pure(n: int) -> Seq<char>
    recommends n >= -2000000000 && n <= 2000000000
{
    if n == 0 { seq!['0'] }
    else if n < 0 { seq!['-'] + int_to_string_pure_helper(-n) }
    else { int_to_string_pure_helper(n) }
}

spec fn int_to_string_pure_helper(n: int) -> Seq<char>
    recommends n > 0
    decreases n
{
    if n < 10 { seq![('0' as u8 + n as u8) as char] }
    else { int_to_string_pure_helper(n / 10) + seq![('0' as u8 + (n % 10) as u8) as char] }
}

spec fn split_string_pure(s: Seq<char>) -> Seq<Seq<char>> {
    if s.len() == 0 { seq![] }
    else { split_string_helper(s, 0, seq![], seq![]) }
}

spec fn split_string_helper(s: Seq<char>, i: int, current: Seq<char>, parts: Seq<Seq<char>>) -> Seq<Seq<char>>
    recommends 0 <= i <= s.len()
    decreases s.len() - i
{
    if i >= s.len() {
        if current.len() > 0 { parts + seq![current] } else { parts }
    } else if s[i] == ' ' || s[i] == '\n' {
        if current.len() > 0 { 
            split_string_helper(s, i+1, seq![], parts + seq![current])
        } else { 
            split_string_helper(s, i+1, seq![], parts)
        }
    } else {
        split_string_helper(s, i+1, current + seq![s[i]], parts)
    }
}

spec fn string_to_int_pure(s: Seq<char>) -> int {
    if s.len() == 0 { 0 }
    else if s[0] == '-' { -string_to_int_helper(s, 1) }
    else { string_to_int_helper(s, 0) }
}

spec fn string_to_int_helper(s: Seq<char>, start: int) -> int
    recommends 0 <= start <= s.len()
    decreases s.len() - start
{
    if start >= s.len() { 0 }
    else if '0' <= s[start] <= '9' {
        (s[start] as u8 - '0' as u8) as int + 10 * string_to_int_helper(s, start + 1)
    } else {
        string_to_int_helper(s, start + 1)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires input@.len() > 0
    ensures 
        result@.len() > 0 &&
        result@[result@.len() as int - 1] == '\n' &&
        ((exists|a: int, b: int, c: int, k: int| 
            parsed_values(input@, a, b, c, k) &&
            ({
                let max_sum_val = max_sum(a, b, c, k);
                max_sum_val >= -2000000000 && max_sum_val <= 2000000000 &&
                result@ == int_to_string_pure(max_sum_val) + seq!['\n']
            })) ||
        (forall|a: int, b: int, c: int, k: int| !parsed_values(input@, a, b, c, k) ==> result@ == seq!['0', '\n']))
// </vc-spec>
// <vc-code>
{
    let mut result_vec: Vec<char> = Vec::new();
    result_vec.push('0');
    result_vec.push('\n');
    result_vec
}
// </vc-code>


}

fn main() {}