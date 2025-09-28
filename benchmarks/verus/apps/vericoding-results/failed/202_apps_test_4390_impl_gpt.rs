// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(test_cases: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < test_cases.len() ==> 
        test_cases[i].0 > 0 && test_cases[i].1 > 0
}

spec fn min_moves_to_divisible(a: int, b: int) -> int
    recommends a > 0 && b > 0
{
    (b - a % b) % b
}

spec fn valid_output(test_cases: Seq<(int, int)>, results: Seq<int>) -> bool
    recommends valid_input(test_cases)
{
    results.len() == test_cases.len() &&
    forall|i: int| 0 <= i < results.len() ==> 
        results[i] == min_moves_to_divisible(test_cases[i].0, test_cases[i].1) &&
        results[i] >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): bounds for min_moves_to_divisible */
proof fn lemma_min_moves_bounds(a: int, b: int)
    requires
        a > 0,
        b > 0,
    ensures
        0 <= min_moves_to_divisible(a, b),
        min_moves_to_divisible(a, b) < b,
{
    let m = a % b;
    assert(0 <= m && m < b);
    let r = (b - m) % b;
    assert(0 <= r && r < b);
    assert(min_moves_to_divisible(a, b) == r);
}

/* helper modified by LLM (iteration 5): roundtrip cast int -> i8 -> int for 0 <= x < 128 */
proof fn lemma_int_to_i8_roundtrip_nonneg_lt128(x: int)
    requires
        0 <= x,
        x < 128,
    ensures
        ((x as i8) as int) == x,
{ }

// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
    ensures valid_output(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute result via spec int formula and cast to i8 after proving bounds */
    let n = test_cases.len();
    let mut results: Vec<i8> = Vec::new();
    results.reserve(n);

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i <= n,
            results.len() == i,
            forall|j: int| 0 <= j < i as int ==> (results@[j] as int) == min_moves_to_divisible(test_cases@[j].0 as int, test_cases@[j].1 as int),
            forall|j: int| 0 <= j < i as int ==> (results@[j] as int) >= 0,
        decreases (n as int) - (i as int)
    {
        let (a, b) = test_cases[i];

        proof {
            let si = i as int;
            let mapped = test_cases@.map(|k, pair: (i8, i8)| (pair.0 as int, pair.1 as int));
            assert(0 <= si && si < mapped.len());
            assert(valid_input(mapped));
            assert(mapped[si] == (test_cases@[si].0 as int, test_cases@[si].1 as int));
            assert(mapped[si].0 > 0 && mapped[si].1 > 0);
        }

        let ai: int = a as int;
        let bi: int = b as int;

        let ri: int = min_moves_to_divisible(ai, bi);

        proof {
            lemma_min_moves_bounds(ai, bi);
            assert(0 <= ri);
            assert(bi <= 127);
            assert(ri < bi);
            assert(ri < 127);
            assert(ri < 128);
        }

        let r: i8;
        proof {
            lemma_int_to_i8_roundtrip_nonneg_lt128(ri);
        }
        r = ri as i8;

        proof {
            assert((r as int) == ri);
            assert(ri == min_moves_to_divisible(ai, bi));
        }

        results.push(r);
        i = i + 1;
    }

    results
}
// </vc-code>


}

fn main() {}