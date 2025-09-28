// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_string(n: int) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string(n / 10).add(seq![('0' as int + (n % 10)) as char])
    }
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        reverse_string(s.subrange(1, s.len() as int)).add(seq![s[0]])
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else {
        string_to_int(s.subrange(0, s.len() - 1)) * 10 + ((s[s.len() - 1] as int) - ('0' as int))
    }
}

spec fn sum_of_palindromes(k: int) -> int
    decreases k
{
    if k <= 0 {
        0
    } else if k == 1 {
        let s = int_to_string(1);
        let reversed = reverse_string(s);
        let palindrome = s.add(reversed);
        string_to_int(palindrome)
    } else {
        let s = int_to_string(k);
        let reversed = reverse_string(s);
        let palindrome = s.add(reversed);
        string_to_int(palindrome) + sum_of_palindromes(k - 1)
    }
}

spec fn valid_input(k: int, p: int) -> bool {
    k >= 1 && p >= 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): make_palindrome_spec */
spec fn make_palindrome_spec(n: int) -> int
    decreases n
{
    let s = int_to_string(n);
    let r = reverse_string(s);
    let p = s.add(r);
    string_to_int(p)
}

/* helper modified by LLM (iteration 5): make_palindrome_num */
fn make_palindrome_num(n: i64) -> (result: i64)
    requires
        n >= 0,
        n <= 100000000,
    ensures
        0 <= result,
        (result as int) == make_palindrome_spec(n as int),
{
    let mut m: i128 = n as i128;
    let mut res: i128 = n as i128;
    while m > 0
        invariant
            m >= 0,
            res >= n as i128,
        decreases
            m
    {
        res = res * 10 + (m % 10);
        m = m / 10;
    }
    assert(res <= 9223372036854775807_i128);
    let result: i64 = res as i64;
    result
}

// </vc-helpers>

// <vc-spec>
fn solve(k: i8, p: i8) -> (result: i8)
    requires
        valid_input(k as int, p as int),
    ensures
        0 <= result < p,
        result as int == (sum_of_palindromes(k as int) % (p as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute sum of palindromes modulo p using helper */
    let mut i: i64 = 1;
    let kk: i64 = k as i64;
    let pp: i64 = p as i64;
    let mut acc: i64 = 0;

    assert(pp > 0);

    while i <= kk
        invariant
            1 <= i && i <= kk + 1,
            (acc as int) == (sum_of_palindromes((i - 1) as int) % (pp as int)),
        decreases
            kk - (i - 1)
    {
        let pal: i64 = make_palindrome_num(i);
        acc = (acc + (pal % pp + pp) % pp) % pp;
        i = i + 1;
    }

    let r: i64 = (acc % pp + pp) % pp;
    r as i8
}
// </vc-code>


}
fn main() {}