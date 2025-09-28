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
/* helper modified by LLM (iteration 2):
Implement exec version of int_to_string */
fn int_to_string_exec(n: int) -> Vec<char>
    requires n >= 0,
{
    if n == 0 {
        vec!['0']
    } else if n < 10 {
        vec![('0' as int + n) as char]
    } else {
        let mut s = int_to_string_exec(n / 10);
        s.push(('0' as int + n % 10) as char);
        s
    }
}

/* helper modified by LLM (iteration 2):
Implement reversal of vector */
fn reverse_vec(v: Vec<char>) -> Vec<char> {
    let mut rev = v.clone();
    rev.reverse();
    rev
}

/* helper modified by LLM (iteration 2):
Compute palindrome vector for n */
fn compute_pal_vector(n: int) -> Vec<char> {
    let s = int_to_string_exec(n);
    let rev = reverse_vec(s.clone());
    let mut pal = s;
    pal.extend(rev);
    pal
}

/* helper modified by LLM (iteration 2):
Convert vector to int */
fn string_to_int_exec(s: Vec<char>) -> int {
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else {
        let rev = string_to_int_exec(s[0..s.len()-1].to_vec()) * 10;
        rev + ((s[s.len()-1] as int) - ('0' as int))
    }
}

/* helper modified by LLM (iteration 2):
Recursive sum of palindromes modulo p */
fn sum_pal(k: int, p: int) -> int
    requires k >= 1, p >= 1,
    decreases k,
    ensures result == sum_of_palindromes(k) % p,
    0 <= result && result < p,
{
    if k == 1 {
        let pal_vec = compute_pal_vector(1);
        let pal_int = string_to_int_exec(pal_vec);
        pal_int % p
    } else {
        let pal_vec = compute_pal_vector(k);
        let pal_int = string_to_int_exec(pal_vec);
        let sum_rest = sum_pal(k - 1, p);
        (pal_int % p + sum_rest) % p
    }
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
/* code modified by LLM (iteration 2):
Compute the result using recursive sum_pal */
{
    let sum = sum_pal(k as int, p as int);
    sum as i8
}
// </vc-code>


}
fn main() {}