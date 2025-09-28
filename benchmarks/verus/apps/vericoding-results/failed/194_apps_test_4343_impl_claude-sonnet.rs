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
/* helper modified by LLM (iteration 5): implemented reverse operation manually to avoid &mut parameter issue */
proof fn lemma_pow26_positive(n: nat)
    ensures pow26(n) >= 1
    decreases n
{
    if n == 0 {
    } else {
        lemma_pow26_positive((n - 1) as nat);
    }
}

proof fn lemma_string_to_base26_bounds(s: Seq<char>)
    requires forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] <= 'z'
    ensures string_to_base26(s) < pow26(s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_string_to_base26_bounds(s.subrange(1, s.len() as int));
        lemma_pow26_positive((s.len() - 1) as nat);
    }
}

fn char_to_digit(c: char) -> (result: usize)
    requires 'a' <= c <= 'z'
    ensures result < 26
{
    (c as usize) - ('a' as usize)
}

fn digit_to_char(d: usize) -> (result: char)
    requires d < 26
    ensures 'a' <= result <= 'z'
{
    ((d + ('a' as usize)) as u8) as char
}

fn compute_string_to_base26(s: &Vec<char>) -> (result: usize)
    requires 
        s.len() >= 1,
        forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] <= 'z'
    ensures result == string_to_base26(s@)
{
    let mut result = 0usize;
    let mut power = 1usize;
    let mut i = s.len();
    
    while i > 0
        invariant
            0 <= i <= s.len(),
            power == pow26((s.len() - i) as nat),
            result == string_to_base26(s@.subrange(i as int, s.len() as int))
        decreases i
    {
        i = i - 1;
        let digit = char_to_digit(s[i]);
        result = result + digit * power;
        if i > 0 {
            power = power * 26;
        }
    }
    
    result
}

fn compute_base26_to_string(mut val: usize, k: usize) -> (result: Vec<char>)
    requires k >= 1
    ensures 
        result.len() == k,
        forall|i: int| 0 <= i < k ==> 'a' <= result[i] <= 'z',
        result@ == base26_to_string(val as nat, k as int)
{
    let mut result = Vec::new();
    let mut i = 0usize;
    
    while i < k
        invariant
            0 <= i <= k,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 'a' <= result[j] <= 'z'
        decreases k - i
    {
        let digit = val % 26;
        let c = digit_to_char(digit);
        result.push(c);
        val = val / 26;
        i = i + 1;
    }
    
    let mut reversed = Vec::new();
    let mut j = result.len();
    while j > 0
        invariant
            0 <= j <= result.len(),
            reversed.len() == result.len() - j,
            forall|idx: int| 0 <= idx < reversed.len() ==> 'a' <= reversed[idx] <= 'z'
        decreases j
    {
        j = j - 1;
        reversed.push(result[j]);
    }
    
    reversed
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
    /* code modified by LLM (iteration 5): called proof functions and implemented main logic */
    proof {
        lemma_string_to_base26_bounds(s@);
        lemma_string_to_base26_bounds(t@);
    }
    
    let s_val = compute_string_to_base26(&s);
    let t_val = compute_string_to_base26(&t);
    let median_val = (s_val + t_val) / 2;
    
    compute_base26_to_string(median_val, k)
}
// </vc-code>


}

fn main() {}