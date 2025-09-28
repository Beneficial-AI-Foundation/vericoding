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
/* helper modified by LLM (iteration 2): [verified helper correctness] */
proof fn minutes_until_midnight_is_valid(h: int, m: int)
    requires
        h >= 0, h < 24,
        m >= 0, m < 60,
        !(h == 0 && m == 0),
    ensures
        1 <= minutes_until_midnight(h, m) <= 1439,
{
    let total_minutes = h * 60 + m;

    assert(h <= 23);
    assert(m <= 59);
    assert(h * 60 <= 23 * 60);
    assert(total_minutes <= 23 * 60 + 59);
    assert(total_minutes <= 1439);

    if h > 0 {
        assert(h >= 1);
        assert(h * 60 >= 60);
        assert(total_minutes >= 60);
    } else { // h == 0
        assert(m >= 1);
        assert(total_minutes == m);
    }
    assert(total_minutes >= 1);

    let result = minutes_until_midnight(h, m);
    assert(1 <= total_minutes <= 1439);
    assert(result == 1440 - total_minutes);
    assert(1 <= result <= 1439);
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
/* code modified by LLM (iteration 2): [fixed exec/ghost type errors and implemented logic] */
{
    let mut results: Vec<i16> = Vec::new();
    let mut i: usize = 0;
    while i < test_cases.len()
        invariant
            0 <= i <= test_cases.len(),
            results.len() == i,
            valid_input(test_cases@.map(|_i: int, x: (i8, i8)| (x.0 as int, x.1 as int))),
            forall|j: int| 0 <= j < i ==> 
                #[trigger] results@[j] as int == minutes_until_midnight(test_cases@[j].0 as int, test_cases@[j].1 as int),
        decreases test_cases.len() - i
    {
        let h_exec = test_cases[i].0;
        let m_exec = test_cases[i].1;

        let result = 1440i16 - (h_exec as i16 * 60i16 + m_exec as i16);

        proof {
            let h_spec = test_cases@[i].0 as int;
            let m_spec = test_cases@[i].1 as int;
            assert(result as int == minutes_until_midnight(h_spec, m_spec));

            let tc_spec = test_cases@.map(|_idx: int, x: (i8, i8)| (x.0 as int, x.1 as int));
            assert(valid_input(tc_spec));
            minutes_until_midnight_is_valid(h_spec, m_spec);
        }
        
        results.push(result);
        i = i + 1;
    }
    
    proof {
        let tc_spec = test_cases@.map(|_i: int, x: (i8, i8)| (x.0 as int, x.1 as int));
        assert(valid_input(tc_spec));

        let results_spec = results@.map(|_i: int, x: i16| x as int);
        assert forall|j: int| 0 <= j < results.len() implies 1 <= #[trigger] results_spec[j] && results_spec[j] <= 1439 by {
            let (h, m) = tc_spec[j];
            assert(results_spec[j] == minutes_until_midnight(h, m));
            minutes_until_midnight_is_valid(h, m);
            assert(1 <= minutes_until_midnight(h, m) <= 1439);
        }
        assert(valid_output(results_spec));
    }

    return results;
}
// </vc-code>


}

fn main() {}