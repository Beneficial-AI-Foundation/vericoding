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
/* helper modified by LLM (iteration 5): compute int sum of '7' bits for first k positions */
spec fn lucky_prefix_sum(n: Seq<char>, k: nat) -> int
    requires
        valid_lucky_number(n),
    decreases k
{
    if k == 0 {
        0
    } else {
        let j: nat = (k - 1) as nat;
        let prev = lucky_prefix_sum(n, j);
        let idx: nat = (n.len() - 1 - (j as int)) as nat;
        prev + if n[j as int] == '7' { pow2(idx) as int } else { 0 }
    }
}

/* helper modified by LLM (iteration 5): prove prefix sum equals binary conversion */
proof fn lucky_prefix_eq_binary(n: Seq<char>)
    requires
        valid_lucky_number(n),
    ensures
        lucky_prefix_sum(n, n.len() as nat) == binary_to_int(convert_to_binary(n)),
    decreases n.len()
{
    if n.len() == 0 {
    } else {
        lucky_prefix_eq_binary(n.subrange(1, n.len() as int));
        proof {
            let len = n.len();
            assert(lucky_prefix_sum(n, len as nat) ==
                (if n[0] == '7' {
                    pow2((len - 1) as nat) as int + lucky_prefix_sum(n.subrange(1, len as int), (len - 1) as nat)
                } else {
                    lucky_prefix_sum(n.subrange(1, len as int), (len - 1) as nat)
                })
            );
            assert(binary_to_int(convert_to_binary(n)) ==
                (if n[0] == '7' {
                    pow2((len - 1) as nat) as int + binary_to_int(convert_to_binary(n.subrange(1, len as int)))
                } else {
                    binary_to_int(convert_to_binary(n.subrange(1, len as int)))
                })
            );
            assert(lucky_prefix_sum(n.subrange(1, len as int), (len - 1) as nat) == binary_to_int(convert_to_binary(n.subrange(1, len as int))));
        }
    }
}

/* helper modified by LLM (iteration 5): relate spec pow2 to runtime shift */
proof fn pow2_shift_equiv(n: nat)
    ensures
        pow2(n) as int == (1i128 << (n as usize)) as int,
    decreases n
{
    if n == 0 {
        assert(pow2(0) as int == 1);
        assert((1i128 << (0usize)) as int == 1);
    } else {
        pow2_shift_equiv((n - 1) as nat);
        assert(pow2(n) as int == 2 * pow2((n - 1) as nat) as int);
        assert((1i128 << (n as usize)) as int == 2 * (1i128 << ((n - 1) as usize)) as int);
        assert(pow2(n) as int == (1i128 << (n as usize)) as int);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: Vec<char>) -> (result: i8)
    requires valid_lucky_number(n@)
    ensures valid_result(n@, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute runtime integer using shifts and maintain invariant relating acc to lucky_prefix_sum */
{
    let len = n.len();
    let mut acc: i64 = 0;
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            acc as int == lucky_prefix_sum(n@, i as nat),
        decreases len - i
    {
        let prev_acc = acc;
        let bit: i64 = if n[i] == '7' { 1 } else { 0 };
        let shift = (len - i - 1) as usize;
        let add = bit << shift;
        acc = prev_acc + add;
        proof {
            assert(prev_acc as int == lucky_prefix_sum(n@, i as nat));
            if n@[i as int] == '7' {
                pow2_shift_equiv((len - i - 1) as nat);
                assert((add as int) == pow2((len - i - 1) as nat) as int);
                assert(acc as int == lucky_prefix_sum(n@, (i + 1) as nat));
            } else {
                assert((add as int) == 0);
                assert(acc as int == lucky_prefix_sum(n@, (i + 1) as nat));
            }
        }
        i = i + 1;
    }
    let two_power_lenminus1: i64 = 1i64 << (len - 1);
    let result_int: i64 = 2 * (two_power_lenminus1 - 1) + acc + 1;
    proof {
        lucky_prefix_eq_binary(n@);
        assert(acc as int == binary_to_int(convert_to_binary(n@)));
        pow2_shift_equiv((len - 1) as nat);
        assert((two_power_lenminus1 as int) == pow2((len - 1) as nat) as int);
        assert((result_int as int) == 2 * (pow2((len - 1) as nat) as int - 1) + acc as int + 1);
    }
    (result_int as i8)
}

// </vc-code>


}

fn main() {}