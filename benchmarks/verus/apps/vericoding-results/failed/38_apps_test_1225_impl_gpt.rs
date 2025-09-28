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
/* helper modified by LLM (iteration 4): trivial lemma to keep helper section valid without affecting logic */
proof fn helper_trivial()
    ensures
        true,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (output: Vec<u8>)
    requires stdin_input@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): removed unsupported saturating_* ops; use plain arithmetic and maintain simple invariants */
    let total_len: usize = stdin_input.len();
    let mut i: usize = 0;
    let mut acc: u64 = 0;
    while i < total_len
        invariant
            i as int <= total_len as int,
        decreases (total_len as int - i as int)
    {
        let b: u8 = stdin_input[i];
        if b == 10 || b == 32 {
            break;
        } else if 48 <= b && b <= 57 {
            acc = acc * 10 + ((b - 48) as u64);
        }
        i = i + 1;
    }

    let mut hh: u64 = acc;
    let mut res: u64 = 0;
    let mut pow: u64 = 1;
    while 0 < hh
        invariant
            pow as int >= 1,
        decreases (hh as int)
    {
        res = res + pow;
        hh = hh / 2;
        pow = pow * 2;
    }

    let mut out: Vec<u8> = Vec::new();
    if res == 0 {
        out.push(48);
    } else {
        let mut tmp: Vec<u8> = Vec::new();
        let mut rr: u64 = res;
        while rr > 0
            decreases (rr as int)
        {
            let d: u8 = (rr % 10) as u8;
            let ch: u8 = 48 + d;
            tmp.push(ch);
            rr = rr / 10;
        }

        let tmp_len: usize = tmp.len();
        let mut j: usize = tmp_len;
        while j > 0
            invariant
                j as int <= tmp_len as int,
            decreases (j as int)
        {
            let b: u8 = tmp[j - 1];
            out.push(b);
            j = j - 1;
        }
    }

    out.push(10);
    out
}
// </vc-code>


}

fn main() {}