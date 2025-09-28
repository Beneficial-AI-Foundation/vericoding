// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(test_cases: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < test_cases.len() ==> 
        #[trigger] test_cases[i].0 >= 0 && 
        test_cases[i].0 < 24 && 
        test_cases[i].1 >= 0 && 
        test_cases[i].1 < 60 && 
        !(test_cases[i].0 == 0 && test_cases[i].1 == 0)
}

spec fn minutes_until_midnight(h: int, m: int) -> int {
    1440 - (h * 60 + m)
}

spec fn valid_output(results: Seq<int>) -> bool {
    forall|i: int| 0 <= i < results.len() ==> 
        1 <= #[trigger] results[i] && results[i] <= 1439
}
// </vc-preamble>

// <vc-helpers>
proof fn input_bounds_for_index(test_cases: &Vec<(i8, i8)>, i: usize)
    requires
        valid_input(test_cases@.map(|j: int, x: (i8, i8)| (x.0 as int, x.1 as int))),
        i < test_cases.len(),
    ensures
        0 <= test_cases[i].0 as int,
        test_cases[i].0 as int < 24,
        0 <= test_cases[i].1 as int,
        test_cases[i].1 as int < 60,
        !(test_cases[i].0 as int == 0 && test_cases[i].1 as int == 0),
{
    let i_int: int = i as int;
    let mapped = test_cases@.map(|j: int, x: (i8, i8)| (x.0 as int, x.1 as int));
    assert(0 <= i_int && i_int < mapped.len());
    assert(valid_input(mapped));
    // Instantiate the quantifier from valid_input at i_int
    assert(mapped[i_int].0 >= 0);
    assert(mapped[i_int].0 < 24);
    assert(mapped[i_int].1 >= 0);
    assert(mapped[i_int].1 < 60);
    assert(!(mapped[i_int].0 == 0 && mapped[i_int].1 == 0));
    // Relate mapped sequence back to the vector elements
    assert(mapped[i_int].0 == test_cases@[i_int].0 as int);
    assert(mapped[i_int].1 == test_cases@[i_int].1 as int);
    assert(test_cases@[i_int] == test_cases[i]);
}

proof fn minutes_bounds_from_valid(h: int, m: int)
    requires
        0 <= h, h < 24,
        0 <= m, m < 60,
        !(h == 0 && m == 0),
    ensures
        1 <= minutes_until_midnight(h, m),
        minutes_until_midnight(h, m) <= 1439,
{
    let total: int = h * 60 + m;
    if h == 0 {
        assert(m != 0);
        assert(m > 0);
        assert(total >= 1); // 0*60 + m >= 1
    } else {
        assert(h >= 1);
        assert(total >= 60);
        assert(total >= 1);
    }
    assert(h <= 23);
    assert(m <= 59);
    assert(total <= 23 * 60 + 59);
    let minutes: int = 1440 - total;
    assert(1 <= minutes);
    assert(minutes <= 1439);
    assert(minutes == minutes_until_midnight(h, m));
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8)>) -> (results: Vec<i16>)
    requires 
        valid_input(test_cases@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)))
    ensures 
        results.len() == test_cases.len(),
        forall|i: int| 0 <= i < results.len() ==> 
            #[trigger] results[i] as int == minutes_until_midnight(test_cases[i].0 as int, test_cases[i].1 as int),
        valid_output(results@.map(|i: int, x: i16| x as int))
// </vc-spec>
// <vc-code>
{
    let mut results: Vec<i16> = Vec::new();
    let mut k: usize = 0;
    while k < test_cases.len()
        invariant
            results.len() == k,
            k <= test_cases.len(),
            forall|j: int| 0 <= j && j < results.len() ==> results[j] as int == minutes_until_midnight(test_cases[j].0 as int, test_cases[j].1 as int),
            forall|j: int| 0 <= j && j < results.len() ==> 1 <= results[j] as int && results[j] as int <= 1439,
        decreases test_cases.len() - k
    {
        let pair = test_cases[k];
        // Prove input bounds for this index
        input_bounds_for_index(&test_cases, k);
        let h: int = pair.0 as int;
        let m: int = pair.1 as int;
        // Establish bounds on the resulting minutes
        minutes_bounds_from_valid(h, m);
        let minutes: int = minutes_until_midnight(h, m);
        // Safe cast to i16
        assert(1 <= minutes && minutes <= 1439);
        assert(-32768 <= minutes && minutes <= 32767);
        let r: i16 = minutes as i16;
        results.push(r);
        // Help the prover about the just-pushed element
        let last_idx: usize = results.len() - 1;
        assert(last_idx as int == k as int);
        assert(results[last_idx] as int == minutes);
        assert(minutes == minutes_until_midnight(h, m));
        k = k + 1;
    }

    // Reify facts for postconditions
    proof {
        assert(forall|i: int| 0 <= i && i < results.len() ==> results[i] as int == minutes_until_midnight(test_cases[i].0 as int, test_cases[i].1 as int));
        assert(forall|i: int| 0 <= i && i < results.len() ==> 1 <= results[i] as int && results[i] as int <= 1439);
    }

    results
}
// </vc-code>


}

fn main() {}