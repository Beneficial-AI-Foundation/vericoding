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
/* helper modified by LLM (iteration 5): Fixed type conversion from int to ghost */
proof fn lemma_pow2_monotonic(n: nat, m: nat)
    requires n <= m,
    ensures pow2(n) <= pow2(m)
    decreases m - n
{
    if n < m {
        lemma_pow2_monotonic(n, m - 1);
        assert(pow2(m - 1) <= pow2(m));
    }
}

proof fn lemma_compute_attacks_iterative_monotonic(h1: int, h2: int, n: int)
    requires
        h1 >= 0,
        h2 >= 0,
        n >= 0,
        h1 <= h2,
    ensures compute_attacks_iterative(h1, n) <= compute_attacks_iterative(h2, n)
    decreases h1 when h1 > 0
{
    if h1 > 0 && h2 > 0 {
        lemma_compute_attacks_iterative_monotonic(h1 / 2, h2 / 2, n + 1);
        lemma_pow2_monotonic(n as nat, n as nat);
    }
}

proof fn lemma_compute_attacks_monotonic(h1: int, h2: int)
    requires
        h1 >= 0,
        h2 >= 0,
        h1 <= h2,
    ensures compute_attacks(h1) <= compute_attacks(h2)
{
    if h1 == 0 {
        assert(compute_attacks(h1) == 0);
    } else {
        lemma_compute_attacks_iterative_monotonic(h1, h2, 0);
    }
}

fn parse_int(s: &[u8]) -> (result: int)
    requires s@.len() > 0,
    ensures result == parse_int_func(s@.map(|c| c as char)),
{
    let mut i: usize = 0;
    let mut acc: int = 0;
    while i < s.len() && s[i] != b'\n' && s[i] != b' '
        invariant
            0 <= i <= s@.len(),
            acc >= 0,
            acc == parse_int_helper(s@.map(|c| c as char), i as int, 0),
    {
        let digit_char = s[i] as char;
        if '0' <= digit_char <= '9' {
            ghost let digit_val: int = (digit_char as u8 - b'0') as int;
            acc = acc * 10 + digit_val;
        }
        i = i + 1;
    }
    acc
}

fn int_to_string(n: int) -> (result: Vec<u8>)
    requires n >= 0,
    ensures result@ == int_to_string_func(n),
{
    if n == 0 {
        return vec![b'0'];
    }
    
    let mut num = n;
    let mut digits: Vec<u8> = Vec::new();
    
    while num > 0
        invariant
            num >= 0,
            digits@.len() > 0 || n > 0,
    {
        let digit = (num % 10) as u8;
        digits.push(b'0' + digit);
        num = num / 10;
    }
    
    digits.reverse();
    digits
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (output: Vec<u8>)
    requires stdin_input@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed parsing and type handling */
    let h_val = parse_int(&stdin_input);
    
    proof {
        assert(valid_input(h_val));
    }
    
    let attacks = compute_attacks(h_val);
    
    proof {
        lemma_compute_attacks_monotonic(1, h_val);
    }
    
    let output_str = int_to_string(attacks);
    output_str
}
// </vc-code>


}

fn main() {}