// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(h: int) -> bool {
    h >= 1
}

spec fn compute_attacks(h: int) -> int
    recommends h >= 0
{
    if h == 0 { 0 }
    else { compute_attacks_iterative(h, 0) }
}

spec fn compute_attacks_iterative(h: int, n: int) -> int
    recommends h >= 0 && n >= 0
    decreases h when h > 0
{
    if h == 0 { 0 }
    else { pow2(n) + compute_attacks_iterative(h / 2, n + 1) }
}

spec fn pow2(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 { 1 }
    else { 2 * pow2(n - 1) }
}

spec fn parse_int_func(s: Seq<char>) -> int
    recommends s.len() > 0
{
    parse_int_helper(s, 0, 0)
}

spec fn parse_int_helper(s: Seq<char>, i: int, acc: int) -> int
    recommends 0 <= i <= s.len() && acc >= 0
    decreases s.len() - i
{
    if i >= s.len() || s[i] == '\n' || s[i] == ' ' {
        acc
    } else if '0' <= s[i] <= '9' {
        parse_int_helper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    } else {
        parse_int_helper(s, i + 1, acc)
    }
}

spec fn int_to_string_func(n: int) -> Seq<char>
    recommends n >= 0
{
    if n == 0 { seq!['0'] }
    else { int_to_string_helper(n, seq![]) }
}

spec fn int_to_string_helper(n: int, acc: Seq<char>) -> Seq<char>
    recommends n >= 0
    decreases n when n > 0
{
    if n == 0 { acc }
    else {
        let digit = n % 10;
        let digit_char = ('0' as int + digit) as char;
        int_to_string_helper(n / 10, seq![digit_char].add(acc))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed int literal syntax errors */
fn lemma_pow2_positive(n: int)
    requires n >= 0
    ensures pow2(n) > 0
    decreases n
{
    if n <= 0 {
    } else {
        lemma_pow2_positive(n - 1);
    }
}

fn lemma_compute_attacks_positive(h: int, n: int)
    requires h > 0, n >= 0
    ensures compute_attacks_iterative(h, n) > 0
    decreases h when h > 0
{
    lemma_pow2_positive(n);
    if h > 1 {
        lemma_compute_attacks_positive(h / 2, n + 1);
    }
}

fn parse_int(s: &Vec<u8>) -> (result: usize)
    requires s@.len() > 0
    ensures result >= 0
{
    let mut acc: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            acc >= 0,
    {
        let c = s[i] as char;
        if c == '\n' || c == ' ' {
            break;
        } else if '0' <= c <= '9' {
            let digit = (c as u8 - b'0') as usize;
            acc = acc * 10 + digit;
        }
        i = i + 1;
    }
    
    acc
}

fn int_to_vec_u8(n: usize) -> (result: Vec<u8>)
    requires n >= 0
    ensures result@.len() > 0
{
    if n == 0 {
        return vec![b'0'];
    }
    
    let mut digits: Vec<u8> = Vec::new();
    let mut temp = n;
    
    while temp > 0
        invariant
            temp >= 0,
    {
        let digit = temp % 10;
        let digit_char = (b'0' + digit as u8);
        digits.push(digit_char);
        temp = temp / 10;
    }
    
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = digits.len();
    
    while i > 0
        invariant
            i <= digits.len(),
    {
        i = i - 1;
        result.push(digits[i]);
    }
    
    result
}

fn compute_attacks_exec(h: usize) -> (result: usize)
    requires h >= 1
    ensures result > 0
{
    proof {
        lemma_compute_attacks_positive(h as int, 0);
    }
    
    let mut total: usize = 0;
    let mut remaining = h;
    let mut power_of_two: usize = 1;
    
    while remaining > 0
        invariant
            remaining >= 0,
            power_of_two > 0,
            total >= 0,
    {
        total = total + power_of_two;
        remaining = remaining / 2;
        power_of_two = power_of_two * 2;
    }
    
    total
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (output: Vec<u8>)
    requires stdin_input@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): same implementation as iteration 4 */
    let h = parse_int(&stdin_input);
    
    if h < 1 {
        return vec![b'0', b'\n'];
    }
    
    let attacks = compute_attacks_exec(h);
    let mut result = int_to_vec_u8(attacks);
    result.push(b'\n');
    
    result
}
// </vc-code>


}

fn main() {}