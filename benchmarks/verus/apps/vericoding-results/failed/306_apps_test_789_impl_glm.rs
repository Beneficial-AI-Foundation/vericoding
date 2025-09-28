// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_lucky_number(n: Seq<char>) -> bool {
    n.len() > 0 && forall|i: int| 0 <= i < n.len() ==> n[i] == '4' || n[i] == '7'
}

spec fn convert_to_binary(n: Seq<char>) -> Seq<char>
    recommends forall|i: int| 0 <= i < n.len() ==> n[i] == '4' || n[i] == '7'
    decreases n.len()
{
    if n.len() == 0 {
        Seq::empty()
    } else if n[0] == '4' {
        seq!['0'].add(convert_to_binary(n.subrange(1, n.len() as int)))
    } else {
        seq!['1'].add(convert_to_binary(n.subrange(1, n.len() as int)))
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

spec fn binary_to_int(s: Seq<char>) -> int
    recommends forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == '1' {
        pow2((s.len() - 1) as nat) + binary_to_int(s.subrange(1, s.len() as int))
    } else {
        binary_to_int(s.subrange(1, s.len() as int))
    }
}

spec fn valid_result(n: Seq<char>, result: int) -> bool
    recommends valid_lucky_number(n)
{
    result > 0 && result == 2 * (pow2((n.len() - 1) as nat) - 1) + binary_to_int(convert_to_binary(n)) + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use executable types (usize, i32) and take slice */
fn exec_pow2(n: usize) -> (result: usize)
    ensures result == pow2(n as nat)
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * exec_pow2(n - 1)
    }
}

/* helper modified by LLM (iteration 4): changed recommends to requires */
fn compute_binary_rec(s: &[char]) -> (value: i32)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] == '4' || s[i] == '7'
    ensures value == binary_to_int(convert_to_binary(s@))
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let (_, rest_slice) = s.split_at(1);
        let rest = compute_binary_rec(rest_slice);
        if s[0] == '4' {
            rest
        } else {
            (exec_pow2(s.len() - 1) as i32) + rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: Vec<char>) -> (result: i8)
    requires valid_lucky_number(n@)
    ensures valid_result(n@, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed slice creation to avoid index operator error */
{
    let L = n.len();
    // Compute base = 2^L - 1
    let base = (1 << L) - 1;
    let bin_value = compute_binary_rec(n.as_slice());
    let total = (base as i32) + bin_value;
    total as i8
}
// </vc-code>


}

fn main() {}