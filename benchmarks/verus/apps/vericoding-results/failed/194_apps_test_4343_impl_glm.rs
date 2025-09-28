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
/* helper modified by LLM (iteration 2): changed nat/int to u64 for executable arithmetic */
fn exec_pow26(n: u64) -> (result: u64)
    ensures result as nat == pow26(n as nat),
    decreases n,
{
    if n == 0 {
        1
    } else {
        26 * exec_pow26(n - 1)
    }
}

/* helper modified by LLM (iteration 5): replaced split_at with slice indexing */
fn exec_string_to_base26(s: &[char]) -> (result: u64)
    requires 
        forall|i: int| 0 <= i < s.len() ==> 'a' <= s@[i] <= 'z',
    ensures 
        result as nat == string_to_base26(s@),
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        let first_char = s[0];
        let rest = &s[1..];
        let first_char_val = (first_char as u32 - 'a' as u32) as u64;
        let power = exec_pow26((s.len() - 1) as u64);
        let rest_val = exec_string_to_base26(rest);
        first_char_val * power + rest_val
    }
}

/* helper modified by LLM (iteration 2): changed nat/int to u64 for executable arithmetic */
fn exec_base26_to_string(val: u64, k: usize) -> (result: Vec<char>)
    requires 
        k >= 1,
    ensures 
        result.len() == k,
        forall|i: int| 0 <= i < k ==> 'a' <= result@[i] <= 'z',
        result@ == base26_to_string(val as nat, k as int),
    decreases k,
{
    if k == 1 {
        let c = ((val % 26) as u32 + 'a' as u32) as u8 as char;
        vec![c]
    } else {
        let next_val = val / 26;
        let c = ((val % 26) as u32 + 'a' as u32) as u8 as char;
        let mut res = exec_base26_to_string(next_val, k-1);
        res.push(c);
        res
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
/* code modified by LLM (iteration 5): using helper with fixed slice indexing */
{
    let s_val = exec_string_to_base26(s.as_slice());
    let t_val = exec_string_to_base26(t.as_slice());
    let median_val = (s_val + t_val) / 2;
    let result = exec_base26_to_string(median_val, k);
    result
}
// </vc-code>


}

fn main() {}