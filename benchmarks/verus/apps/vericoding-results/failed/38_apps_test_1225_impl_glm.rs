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
/* helper modified by LLM (iteration 5): changed to use Vec<u8> for executable parsing and string conversion */
fn pow2_exec(n: u64) -> (result: u64)
    ensures result as int == pow2(n as int)
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2_exec(n - 1)
    }
}

fn compute_attacks_iterative_exec(h: u64, n: u64) -> (result: u64)
    ensures result as int == compute_attacks_iterative(h as int, n as int)
    decreases h when h > 0
{
    if h == 0 {
        0
    } else {
        pow2_exec(n) + compute_attacks_iterative_exec(h / 2, n + 1)
    }
}

fn compute_attacks_exec(h: u64) -> (result: u64)
    requires h >= 1
    ensures result as int == compute_attacks(h as int)
{
    compute_attacks_iterative_exec(h, 0)
}

fn parse_int_vec(s: Vec<u8>) -> (result: u64) {
    let mut i: usize = 0;
    let mut acc: u64 = 0;
    while i < s.len() {
        let b = s[i];
        if b == b'\n' || b == b' ' {
            break;
        } else if b'0' <= b && b <= b'9' {
            let digit = (b - b'0') as u64;
            acc = acc * 10 + digit;
        }
        i += 1;
    }
    acc
}

fn int_to_string_vec(n: u64) -> (v: Vec<u8>) {
    if n == 0 {
        vec![b'0']
    } else {
        let mut v = Vec::new();
        let mut n = n;
        while n > 0 {
            let digit = n % 10;
            let digit_char = b'0' + digit as u8;
            v.push(digit_char);
            n /= 10;
        }
        v.reverse();
        v
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (output: Vec<u8>)
    requires stdin_input@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): adjusted to use new helper functions that work on Vec<u8> */
    let h = parse_int_vec(stdin_input);
    let attacks = compute_attacks_exec(h);
    let output_vec = int_to_string_vec(attacks);
    output_vec
}
// </vc-code>


}

fn main() {}