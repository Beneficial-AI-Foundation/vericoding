// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(k: int) -> bool {
    2 <= k <= 100
}

spec fn count_odd_numbers(k: int) -> int
    recommends k >= 1
{
    (k + 1) / 2
}

spec fn count_even_numbers(k: int) -> int
    recommends k >= 1
{
    k / 2
}

spec fn expected_result(k: int) -> int
    recommends valid_input(k)
{
    count_odd_numbers(k) * count_even_numbers(k)
}

spec fn correct_result(k: int, result: int) -> bool
    recommends valid_input(k)
{
    result == expected_result(k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): establish non-negativity of counts */
proof fn lemma_counts_nonneg(k: int)
    requires
        k >= 1,
    ensures
        count_odd_numbers(k) >= 0,
        count_even_numbers(k) >= 0,
{
    assert(k / 2 >= 0);
    assert((k + 1) / 2 >= 0);
}

/* helper modified by LLM (iteration 5): expected_result is non-negative for valid inputs */
proof fn lemma_expected_nonneg(k: int)
    requires
        valid_input(k),
    ensures
        expected_result(k) >= 0,
{
    lemma_counts_nonneg(k);
    assert(expected_result(k) == count_odd_numbers(k) * count_even_numbers(k));
    assert(count_odd_numbers(k) >= 0);
    assert(count_even_numbers(k) >= 0);
    assert(expected_result(k) >= 0);
}

/* helper modified by LLM (iteration 5): connect expected_result to its defining product explicitly */
proof fn lemma_expected_is_product(k: int)
    requires
        valid_input(k),
    ensures
        expected_result(k) == count_odd_numbers(k) * count_even_numbers(k),
{
    assert(expected_result(k) == count_odd_numbers(k) * count_even_numbers(k));
}

/* helper modified by LLM (iteration 5): division by 2 is monotonic on non-negative integers */
proof fn lemma_div2_monotone_nonneg(x: int, y: int)
    requires
        0 <= x,
        x <= y,
    ensures
        x / 2 <= y / 2,
        (x + 1) / 2 <= (y + 1) / 2,
{
    assert(x / 2 <= y / 2);
    assert((x + 1) / 2 <= (y + 1) / 2);
}
// </vc-helpers>

// <vc-spec>
fn count_even_odd_pairs(k: i8) -> (result: i8)
    requires
        valid_input(k as int),
    ensures
        correct_result(k as int, result as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute product in i16 and prove correctness; cast to i8 only when it fits, otherwise abort */
    let k16: i16 = k as i16;
    let odds16: i16 = (k16 + 1) / 2;
    let evens16: i16 = k16 / 2;
    let prod16: i16 = odds16 * evens16;

    proof {
        let ghost ki: int = k as int;
        assert(valid_input(ki));
        lemma_expected_is_product(ki);

        // Relate machine computations to mathematical ints
        assert(((k16 + 1) as int) == ki + 1);
        assert(0 <= ((k16 + 1) as int));
        assert((((k16 + 1) / 2) as int) == (((k16 + 1) as int) / 2));
        assert((odds16 as int) == (ki + 1) / 2);

        assert((k16 as int) == ki);
        assert(0 <= (k16 as int));
        assert(((k16 / 2) as int) == ((k16 as int) / 2));
        assert((evens16 as int) == ki / 2);

        // Show product cast equals product of casts (no overflow)
        lemma_div2_monotone_nonneg(ki, 100);
        lemma_div2_monotone_nonneg(ki + 1, 101);
        assert((evens16 as int) <= 50);
        assert((odds16 as int) <= 50);
        assert((evens16 as int) >= 0);
        assert((odds16 as int) >= 0);
        assert(((evens16 as int) * (odds16 as int)) <= 2500);
        assert(-32768 <= ((odds16 as int) * (evens16 as int)) && ((odds16 as int) * (evens16 as int)) <= 32767);
        assert(((odds16 * evens16) as int) == (odds16 as int) * (evens16 as int));
        assert((prod16 as int) == (odds16 as int) * (evens16 as int));
        assert((prod16 as int) == expected_result(ki));
    }

    if 0 <= prod16 && prod16 <= 127 {
        let r: i8 = prod16 as i8;
        proof {
            let ghost ki: int = k as int;
            assert((r as int) == (prod16 as int));
            assert((r as int) == expected_result(ki));
            assert(r >= 0);
        }
        r
    } else {
        assert(false);
        unreached()
    }
}
// </vc-code>


}

fn main() {}