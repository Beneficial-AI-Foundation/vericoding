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
/* helper modified by LLM (iteration 5): parse bytes to i64 */
fn parse_int_from_bytes(s: &Vec<u8>) -> i64
    requires
        s@.len() > 0,
    ensures
        result >= 0,
{
    let len: usize = s.len();
    let mut i: usize = 0;
    let mut acc: i64 = 0;
    while i < len
        invariant
            i <= len,
            acc >= 0,
        decreases len - i
    {
        let c: u8 = s[i];
        if c == 10u8 || c == 32u8 {
            i = len;
        } else if c >= 48u8 && c <= 57u8 {
            acc = acc * 10 + (c as i64 - 48);
            i = i + 1;
        } else {
            i = i + 1;
        }
    }
    let result = acc;
    result
}

/* helper modified by LLM (iteration 5): convert i64 to bytes */
fn int_to_bytes(n: i64) -> Vec<u8>
    requires
        n >= 0,
    ensures
        result.len() > 0,
{
    if n == 0 {
        let mut v: Vec<u8> = Vec::new();
        v.push(48u8);
        let result = v;
        result
    } else {
        let mut v: Vec<u8> = Vec::new();
        let mut m: i64 = n;
        while m > 0
            invariant
                m >= 0,
                v.len() >= 0,
            decreases m
        {
            let digit = (m % 10) as u8;
            v.push(48u8 + digit);
            m = m / 10;
        }
        let mut res: Vec<u8> = Vec::new();
        let mut j: usize = v.len();
        while j > 0
            invariant
                j <= v.len(),
                res.len() + j == v.len(),
            decreases j
        {
            j = j - 1;
            res.push(v[j]);
        }
        let result = res;
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (output: Vec<u8>)
    requires stdin_input@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): parse input, compute attacks, format output */
    let h = parse_int_from_bytes(&stdin_input);
    let attacks: i64;
    if h == 0 {
        attacks = 0;
    } else {
        let mut t: i64 = h;
        let mut k: usize = 0;
        while t > 0
            invariant
                t >= 0,
            decreases t
        {
            t = t / 2;
            k = k + 1;
        }
        let mut pow: i64 = 1;
        let mut i: usize = 0;
        while i < k
            invariant
                pow >= 1,
                i <= k,
            decreases k - i
        {
            pow = pow * 2;
            i = i + 1;
        }
        attacks = pow - 1;
    }
    let mut out = int_to_bytes(attacks);
    out.push(10u8);
    out
}
// </vc-code>


}

fn main() {}