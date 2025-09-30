// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 16
}

spec fn fact_truth_values() -> Seq<int> {
    seq![1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0]
}

spec fn valid_output(result: int) -> bool {
    result == 0 || result == 1
}

spec fn expected_output(n: int) -> int
    recommends valid_input(n)
{
    fact_truth_values()[n - 1]
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_expected_output_cases(n: int)
    requires
        valid_input(n)
    ensures
        (n == 1) ==> expected_output(n) == 1,
        (n == 2) ==> expected_output(n) == 0,
        (n == 3) ==> expected_output(n) == 0,
        (n == 4) ==> expected_output(n) == 1,
        (n == 5) ==> expected_output(n) == 0,
        (n == 6) ==> expected_output(n) == 1,
        (n == 7) ==> expected_output(n) == 0,
        (n == 8) ==> expected_output(n) == 1,
        (n == 9) ==> expected_output(n) == 1,
        (n == 10) ==> expected_output(n) == 1,
        (n == 11) ==> expected_output(n) == 0,
        (n == 12) ==> expected_output(n) == 0,
        (n == 13) ==> expected_output(n) == 1,
        (n == 14) ==> expected_output(n) == 0,
        (n == 15) ==> expected_output(n) == 1,
        (n == 16) ==> expected_output(n) == 0,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        valid_output(result as int),
        result as int == expected_output(n as int)
// </vc-spec>
// <vc-code>
{
    let res: i8 =
        if n == 1 { 1i8 }
        else if n == 2 { 0i8 }
        else if n == 3 { 0i8 }
        else if n == 4 { 1i8 }
        else if n == 5 { 0i8 }
        else if n == 6 { 1i8 }
        else if n == 7 { 0i8 }
        else if n == 8 { 1i8 }
        else if n == 9 { 1i8 }
        else if n == 10 { 1i8 }
        else if n == 11 { 0i8 }
        else if n == 12 { 0i8 }
        else if n == 13 { 1i8 }
        else if n == 14 { 0i8 }
        else if n == 15 { 1i8 }
        else if n == 16 { 0i8 }
        else { 0i8 };

    proof {
        lemma_expected_output_cases(n as int);
        if n == 1 {
            assert(res as int == 1);
            assert(expected_output(n as int) == 1);
        } else if n == 2 {
            assert(res as int == 0);
            assert(expected_output(n as int) == 0);
        } else if n == 3 {
            assert(res as int == 0);
            assert(expected_output(n as int) == 0);
        } else if n == 4 {
            assert(res as int == 1);
            assert(expected_output(n as int) == 1);
        } else if n == 5 {
            assert(res as int == 0);
            assert(expected_output(n as int) == 0);
        } else if n == 6 {
            assert(res as int == 1);
            assert(expected_output(n as int) == 1);
        } else if n == 7 {
            assert(res as int == 0);
            assert(expected_output(n as int) == 0);
        } else if n == 8 {
            assert(res as int == 1);
            assert(expected_output(n as int) == 1);
        } else if n == 9 {
            assert(res as int == 1);
            assert(expected_output(n as int) == 1);
        } else if n == 10 {
            assert(res as int == 1);
            assert(expected_output(n as int) == 1);
        } else if n == 11 {
            assert(res as int == 0);
            assert(expected_output(n as int) == 0);
        } else if n == 12 {
            assert(res as int == 0);
            assert(expected_output(n as int) == 0);
        } else if n == 13 {
            assert(res as int == 1);
            assert(expected_output(n as int) == 1);
        } else if n == 14 {
            assert(res as int == 0);
            assert(expected_output(n as int) == 0);
        } else if n == 15 {
            assert(res as int == 1);
            assert(expected_output(n as int) == 1);
        } else if n == 16 {
            assert(res as int == 0);
            assert(expected_output(n as int) == 0);
        }
    }

    assert(res as int == 0 || res as int == 1);

    res
}
// </vc-code>


}

fn main() {}