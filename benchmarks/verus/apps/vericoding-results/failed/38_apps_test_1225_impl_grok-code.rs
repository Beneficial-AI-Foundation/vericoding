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
fn pow2_exec(n: u32) -> u64
    requires n < 64
    ensures pow2(n as int) == result as int
{
    let mut res: u64 = 1;
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            res as int == pow2(i as int),
        decreases n - i
    {
        res = res * 2;
        i += 1;
    }
    res
}

/* helper modified by LLM (iteration 3): fixed compilation errors: escaped characters and ensures syntax */
fn parse_u32(input_: &Vec<u8>) -> u32
{
    let s = input_@;
    let mut i: usize = 0;
    let mut acc: u32 = 0;
    while i < s.len() && s[i] != ' ' as u8 && s[i] != '\n' as u8
        invariant i <= s.len()
        decreases s.len() - i
    {
        if s[i] >= '0' as u8 && s[i] <= '9' as u8 {
            acc = acc * 10 + (s[i] - '0' as u8) as u32;
        }
        i += 1;
    }
    acc
}

fn int_to_vec(n: u64) -> Vec<u8>
{
    if n == 0 {
        return vec!['0' as u8];
    }
    let mut digits = Vec::new();
    let mut m = n;
    while m > 0
        invariant m >= 0
        decreases m
    {
        digits.insert(0, ('0' as u8) + (m % 10) as u8);
        m /= 10;
    }
    digits
}

fn compute_attacks_exec(h: u32) -> u64
    requires h >= 1
{
    let mut sum: u64 = 0;
    let mut h_current: u32 = h;
    let mut n: u32 = 0;
    while h_current > 0
        invariant h_current >= 0 && n >= 0
        decreases h_current
    {
        sum += pow2_exec(n);
        h_current /= 2;
        n += 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (output: Vec<u8>)
    requires stdin_input@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation errors: escaped newline character */
    let s = parse_u32(&stdin_input);
    if s >= 1 {
        let attacks = compute_attacks_exec(s);
        let mut out = int_to_vec(attacks);
        out.push('\n' as u8);
        out
    } else {
        vec![]
    }
}
// </vc-code>


}

fn main() {}