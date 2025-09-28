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
    /* code modified by LLM (iteration 5): Fixed assert statement syntax */
    let mut results = Vec::new();
    let mut i = 0;
    while i < test_cases.len()
        invariant
            0 <= i <= test_cases.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] results[j] as int == minutes_until_midnight(test_cases[j].0 as int, test_cases[j].1 as int),
            valid_input(test_cases@.map(|k: int, x: (i8, i8)| (x.0 as int, x.1 as int))),
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] results[j] as int && results[j] as int <= 1439,
        decreases test_cases.len() - i
    {
        let h = test_cases[i].0;
        let m = test_cases[i].1;
        let minutes_remaining = (1440 - (h as i16 * 60 + m as i16)) as i16;
        
        proof {
            // Access the precondition to get bounds on h and m
            let spec_test_cases = test_cases@.map(|k: int, x: (i8, i8)| (x.0 as int, x.1 as int));
            assert(valid_input(spec_test_cases));
            assert(0 <= i < spec_test_cases.len());
            assert(spec_test_cases[i as int].0 >= 0);
            assert(spec_test_cases[i as int].0 < 24);
            assert(spec_test_cases[i as int].1 >= 0);
            assert(spec_test_cases[i as int].1 < 60);
            assert(!(spec_test_cases[i as int].0 == 0 && spec_test_cases[i as int].1 == 0));
            
            // Now we can derive the needed properties
            assert(h as int == spec_test_cases[i as int].0);
            assert(m as int == spec_test_cases[i as int].1);
            assert(0 <= h as int);
            assert(h as int < 24);
            assert(0 <= m as int);
            assert(m as int < 60);
            assert(!(h == 0 && m == 0));
            
            // Rest of the proof
            assert(h as int * 60 + m as int >= 1);
            assert(h as int * 60 + m as int <= 23 * 60 + 59);
            assert(h as int * 60 + m as int <= 1439);
            assert(1440 - (h as int * 60 + m as int) >= 1);
            assert(1440 - (h as int * 60 + m as int) <= 1439);
            assert(minutes_remaining as int == 1440 - (h as int * 60 + m as int));
            assert(1 <= minutes_remaining as int);
            assert(minutes_remaining as int <= 1439);
        }
        
        results.push(minutes_remaining);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}