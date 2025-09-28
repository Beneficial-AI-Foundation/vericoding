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
/* helper modified by LLM (iteration 5): relate computed spec result to min_moves_to_divisible and bound it */
proof fn compute_min_moves_equiv(a: int, b: int, res: int)
    requires
        a > 0,
        b > 0,
        res == (b - a % b) % b,
    ensures
        res == min_moves_to_divisible(a, b),
        0 <= res && res < b,
{
    assert(res == min_moves_to_divisible(a, b));
    assert(0 <= res && res < b);
}

// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
    ensures valid_output(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterate test cases using int index, compute normalized remainder and map to spec with helper */
{
    let n = test_cases.len();
    let n_int: int = n as int;
    let mut i: int = 0;
    let mut results = Vec::<i8>::new();
    while i < n_int
        invariant
            0 <= i && i <= n_int,
            results@.len() == i,
            forall|j: int| 0 <= j < i ==> (results@[j] as int) == min_moves_to_divisible((test_cases@)[j].0 as int, (test_cases@)[j].1 as int) && (results@[j] as int) >= 0,
        decreases n_int - i
    {
        let idx: usize = (i as usize);
        let pair = test_cases[idx];
        let a_i_exe: i32 = pair.0 as i32;
        let b_i_exe: i32 = pair.1 as i32;
        let mut r = a_i_exe % b_i_exe;
        if r < 0 {
            r = r + b_i_exe;
        }
        let res_i_native = (b_i_exe - r) % b_i_exe;
        proof {
            let a_g: int = pair.0 as int;
            let b_g: int = pair.1 as int;
            let res_g: int = res_i_native as int;
            assert(a_i_exe as int == a_g);
            assert(b_i_exe as int == b_g);
            assert((a_i_exe % b_i_exe) as int == a_g % b_g);
            assert(res_g == (b_g - (a_g % b_g)) % b_g);
            compute_min_moves_equiv(a_g, b_g, res_g);
        }
        results.push(res_i_native as i8);
        i = i + 1;
    }
    results
}

// </vc-code>


}

fn main() {}