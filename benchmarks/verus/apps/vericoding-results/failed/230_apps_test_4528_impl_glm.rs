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
fn compute_minutes_until_midnight(h: i8, m: i8) -> (result: i16)
    requires
        h >= 0,
        h < 24,
        m >= 0,
        m < 60,
        !(h == 0 && m == 0),
    ensures
        result as int == minutes_until_midnight(h as int, m as int),
        result >= 1,
        result <= 1439,
{
    /* helper modified by LLM (iteration 3): ensure precondition satisfaction */
    let total_minutes_today = (h as i16) * 60 + (m as i16);
    1440 - total_minutes_today
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
    /* code modified by LLM (iteration 5): fix type mismatches by converting i to int for sequence indexing */
    let mut results = Vec::new();
    let mut i = 0usize;
    while i < test_cases.len()
        invariant
            i <= test_cases.len(),
            results.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> 
                #[trigger] results@[j] as int == minutes_until_midnight(test_cases@[j].0 as int, test_cases@[j].1 as int),
            valid_output(results@.map(|k: int, x: i16| x as int)),
            valid_input(test_cases@.map(|idx: int, x: (i8, i8)| (x.0 as int, x.1 as int)))
        decreases test_cases.len() - i
    {
        let (h, m) = test_cases[i];
        proof {
            assert(#[trigger] test_cases@[i as int].0 >= 0);
            assert(test_cases@[i as int].0 < 24);
            assert(test_cases@[i as int].1 >= 0);
            assert(test_cases@[i as int].1 < 60);
            assert(!(test_cases@[i as int].0 == 0 && test_cases@[i as int].1 == 0));
            assert(h == test_cases@[i as int].0);
            assert(m == test_cases@[i as int].1);
            assert(h >= 0);
            assert(h < 24);
            assert(m >= 0);
            assert(m < 60);
            assert(!(h == 0 && m == 0));
        }
        let minutes = compute_minutes_until_midnight(h, m);
        results.push(minutes);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}