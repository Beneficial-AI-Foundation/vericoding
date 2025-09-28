// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn median_string(s: Seq<char>, t: Seq<char>, k: int) -> Seq<char> {
    let s_val = string_to_base26(s);
    let t_val = string_to_base26(t);
    let median_val = (s_val + t_val) / 2;
    base26_to_string(median_val, k)
}

spec fn string_to_base26(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else { ((s[0] as int - 'a' as int) * pow26((s.len() - 1) as nat) + string_to_base26(s.subrange(1, s.len() as int))) as nat }
}

spec fn base26_to_string(val: nat, k: int) -> Seq<char>
    decreases k when k >= 1
{
    if k == 1 { seq![((val % 26) + ('a' as int)) as char] }
    else { base26_to_string(val / 26, k - 1).add(seq![((val % 26) + ('a' as int)) as char]) }
}

spec fn pow26(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 26 * pow26((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): char to digit conversion */
spec fn char_to_digit(c: char) -> int {
    (c as int) - ('a' as int)
}

/* helper modified by LLM (iteration 5): digit to char conversion */
spec fn digit_to_char(d: int) -> char {
    (d + ('a' as int)) as char
}

/* helper modified by LLM (iteration 5): char digit range lemma */
fn char_digit_range(c: char) -> ()
    requires
        'a' <= c <= 'z',
    ensures
        0 <= char_to_digit(c) <= 25,
{
    proof {
        assert(char_to_digit(c) == (c as int) - ('a' as int));
        assert((c as int) - ('a' as int) >= 0);
        assert((c as int) <= 'z' as int);
        assert((c as int) - ('a' as int) <= ('z' as int) - ('a' as int));
        assert(('z' as int) - ('a' as int) == 25);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(k: usize, s: Vec<char>, t: Vec<char>) -> (result: Vec<char>)
    requires 
        k >= 1,
        s.len() == k,
        t.len() == k,
        forall|i: int| 0 <= i < k ==> 'a' <= #[trigger] s[i] <= 'z',
        forall|i: int| 0 <= i < k ==> 'a' <= #[trigger] t[i] <= 'z',
    ensures 
        result.len() == k,
        forall|i: int| 0 <= i < k ==> 'a' <= #[trigger] result[i] <= 'z',
        result@ == median_string(s@, t@, k as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute median string via base-26 arithmetic */
    let n = #[verifier::truncate] k as int;

    let mut i: int = 0;
    let mut a = Vec::<int>::new();
    while i < n
        invariant
            0 <= i <= n,
            #[verifier::truncate] a.len() as int == i,
        decreases n - i
    {
        let ch = s[#[verifier::truncate] i as usize];
        a.push((ch as int) - ('a' as int));
        i += 1;
    }

    let mut i2: int = 0;
    let mut b = Vec::<int>::new();
    while i2 < n
        invariant
            0 <= i2 <= n,
            #[verifier::truncate] b.len() as int == i2,
        decreases n - i2
    {
        let ch = t[#[verifier::truncate] i2 as usize];
        b.push((ch as int) - ('a' as int));
        i2 += 1;
    }

    let mut s_digits = Vec::<int>::new();
    let mut carry: int = 0;
    let mut p: int = 0;
    while p < n
        invariant
            0 <= p <= n,
            #[verifier::truncate] s_digits.len() as int == p,
            #[verifier::truncate] a.len() as int == n,
            #[verifier::truncate] b.len() as int == n,
        decreases n - p
    {
        let idx = #[verifier::truncate] (n - 1 - p) as usize;
        let sum = a[idx] + b[idx] + carry;
        let digit = sum % 26;
        carry = sum / 26;
        s_digits.push(digit);
        p += 1;
    }

    let mut D = Vec::<int>::new();
    D.push(carry);
    let mut j: int = 0;
    while j < n
        invariant
            0 <= j <= n,
            #[verifier::truncate] D.len() as int == j + 1,
            #[verifier::truncate] s_digits.len() as int == n,
        decreases n - j
    {
        let idx = #[verifier::truncate] (n - 1 - j) as usize;
        D.push(s_digits[idx]);
        j += 1;
    }

    let m = n + 1;
    let mut q = Vec::<int>::new();
    let mut rem: int = 0;
    let mut idx2: int = 0;
    while idx2 < m
        invariant
            0 <= idx2 <= m,
            #[verifier::truncate] q.len() as int == idx2,
            #[verifier::truncate] D.len() as int == m,
        decreases m - idx2
    {
        let cur = rem * 26 + D[#[verifier::truncate] idx2 as usize];
        let qd = cur / 2;
        rem = cur % 2;
        q.push(qd);
        idx2 += 1;
    }

    let mut result = Vec::<char>::new();
    let mut r: int = 1;
    while r <= n
        invariant
            1 <= r <= n + 1,
            #[verifier::truncate] result.len() as int == r - 1,
            #[verifier::truncate] q.len() as int == m,
        decreases n + 1 - r
    {
        let digit = q[#[verifier::truncate] r as usize];
        let ch = (#[verifier::truncate] (digit + ('a' as int)) as u8) as char;
        result.push(ch);
        r += 1;
    }

    result
}

// </vc-code>


}

fn main() {}