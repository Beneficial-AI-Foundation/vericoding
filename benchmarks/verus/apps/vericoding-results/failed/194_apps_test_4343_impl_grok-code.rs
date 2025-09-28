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

/* helper modified by LLM (iteration 2): Added executable pow26 calculation */
fn pow26_exec(n: usize) -> usize
    decreases n
{
    if n == 0 {
        1
    } else {
        26 * pow26_exec(n - 1)
    }
}

/* helper modified by LLM (iteration 2): Added executable string to base26 conversion */
fn exec_string_to_base26(s: Vec<char>) -> usize
    requires
        forall|i| 0 <= i < s.len() ==> 'a' <= s[i] <= 'z'
    ensures
        result as nat == string_to_base26(s@)
{
    exec_string_to_base26_helper(s, s.len())
}

/* helper modified by LLM (iteration 2): Added executable helper for string to base26 conversion */
fn exec_string_to_base26_helper(s: Vec<char>, n: usize) -> usize
    decreases n
    requires
        n <= s.len(),
        forall|i| 0 <= i < s.len() ==> 'a' <= s[i] <= 'z'
    ensures
        result as nat == string_to_base26(s@.subrange(s@.len() - n, s@.len()))
{
    if n == 0 {
        0
    } else {
        let digit = (s[n - 1] as int - 'a' as int) as usize;
        digit + 26 * exec_string_to_base26_helper(s, n - 1)
    }
}

/* helper modified by LLM (iteration 2): Added executable base26 to string conversion */
fn exec_base26_to_string(val: usize, k: usize) -> Vec<char>
    decreases k
    requires
        k >= 1
    ensures
        result@ == base26_to_string(val as nat, k as int),
        result.len() == k
{
    if k == 1 {
        let digit = (('a' as int) + ((val % 26) as int)) as char;
        vec![digit]
    } else {
        let mut res = exec_base26_to_string(val / 26, k - 1);
        let digit = (('a' as int) + ((val % 26) as int)) as char;
        res.push(digit);
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
{
/* code modified by LLM (iteration 2): Implemented median string computation using helper functions */
    let s_val = exec_string_to_base26(s);
    let t_val = exec_string_to_base26(t);
    let median_val = (s_val + t_val) / 2;
    exec_base26_to_string(median_val, k)
}
// </vc-code>


}

fn main() {}