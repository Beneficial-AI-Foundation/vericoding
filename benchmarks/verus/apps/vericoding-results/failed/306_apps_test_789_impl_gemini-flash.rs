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

// </vc-helpers>

// <vc-spec>
fn solve(n: Vec<char>) -> (result: i8)
    requires valid_lucky_number(n@)
    ensures valid_result(n@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by moving pow2 calls into ghost context or ensuring type compatibility with `as int` if used in non-ghost code. */
    let s: Seq<char> = n@;
    let len = s.len();
    let ghost mut binary_val: int = 0;
    let mut i: int = 0;

    while i < len
        invariant
            0 <= i <= len,
            binary_val == binary_to_int(convert_to_binary(s.subrange(0, i as int))),
            s == n@,
            len == n.len(),
    {
        proof {
            if s[i] == '7' {
                assert(binary_val + pow2((len - 1 - i) as nat) == binary_to_int({
                    let mut temp_s = convert_to_binary(s.subrange(0, i as int));
                    temp_s.set(i as int, '1');
                    temp_s
                })) by {
                    // This proof block is just to satisfy the invariant, the actual update is done on the ghost variable
                };
            }
        }
        if s[i] == '7' {
            // This line is within the ghost context due to binary_val being ghost
            binary_val = binary_val + pow2((len - 1 - i) as nat);
        }
        i = i + 1;
    }

    let ghost mut sum_powers_of_2_minus_1: int = 0;

    if len > 0 {
        sum_powers_of_2_minus_1 = pow2(len as nat) - 1;
    }

    let ghost r_int = (sum_powers_of_2_minus_1 * 2 + binary_val + 1);
    
    (r_int) as i8
}
// </vc-code>


}

fn main() {}