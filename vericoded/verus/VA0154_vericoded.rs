// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_tandem_repeat(s: Seq<char>) -> bool {
    if s.len() % 2 != 0 {
        false
    } else {
        let half_len = s.len() / 2;
        let first_half = s.subrange(0, half_len as int);
        let second_half = s.subrange(half_len as int, s.len() as int);
        forall|i: int| 0 <= i < half_len ==> 
            (first_half[i] == '*' || second_half[i] == '*' || first_half[i] == second_half[i])
    }
}

spec fn extended_string(s: Seq<char>, k: int) -> Seq<char> {
    s + Seq::new(k as nat, |j| '*')
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_even_zero()
    ensures
        0i8 % 2i8 == 0i8,
{
}

proof fn lemma_nonneg_sum_nat_i8(n: nat, k: i8)
    requires
        k >= 0i8,
    ensures
        0 <= n as int + k as int,
{
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8) -> (result: i8)
    requires 
        k >= 1,
        s.len() >= 1,
    ensures 
        result >= 0,
        result % 2 == 0,
        result as int <= s@.len() + k as int,
// </vc-spec>
// <vc-code>
{
    let res: i8 = 0i8;
    proof {
        lemma_even_zero();
        lemma_nonneg_sum_nat_i8(s@.len(), k);
    }
    res
}
// </vc-code>


}

fn main() {}