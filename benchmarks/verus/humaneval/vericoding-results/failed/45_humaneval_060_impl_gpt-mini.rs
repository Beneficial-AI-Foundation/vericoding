// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn sum_from_one_to_n(n: int) -> int
    recommends n >= 1
{
    n * (n + 1) / 2
}
// </vc-preamble>

// <vc-helpers>
fn sum_step(i: int)
    requires i >= 1
    ensures (if i == 1 { 0 } else { sum_from_one_to_n(i - 1) }) + i == sum_from_one_to_n(i)
{
    proof {
        if i == 1 {
            // sum_from_one_to_n(1) == 1 by definition
            assert(sum_from_one_to_n(1) == 1);
        } else {
            // unfold definitions and do simple algebra
            assert(sum_from_one_to_n(i - 1) == (i - 1) * i / 2);
            assert(sum_from_one_to_n(i) == i * (i + 1) / 2);
            assert((i - 1) * i / 2 + i == i * (i + 1) / 2);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == sum_from_one_to_n(n as int)
// </vc-spec>
// <vc-code>
{
    let N: int = n as int;
    let mut i: int = 1;
    let mut acc: int = 0;
    while i <= N
        invariant
            1 <= i <= N + 1,
            acc == if i == 1 { 0 } else { sum_from_one_to_n(i - 1) },
        decreases N + 1 - i
    {
        proof {
            // use the lemma to relate acc + i to the sum for i
            sum_step(i);
        }
        acc = acc + i;
        i = i + 1;
    }
    let result: i8 = acc as i8;
    result
}
// </vc-code>


}

fn main() {}