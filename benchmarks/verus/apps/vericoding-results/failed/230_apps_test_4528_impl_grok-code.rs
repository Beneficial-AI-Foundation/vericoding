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
    /* code modified by LLM (iteration 5): changed loop index to usize to avoid casting in exec code */
    let mut results: Vec<i16> = Vec::with_capacity(test_cases.len());
    let mut i: usize = 0;
    while i < test_cases.len()
        invariant
            i as int <= test_cases.len() as int,
            results.len() == i,
            forall|j: int| #![auto] 0 <= j < i as int ==> 
                results@[j] as int == minutes_until_midnight(test_cases@[j].0 as int, test_cases@[j].1 as int),
            forall|j: int| 0 <= j < i as int ==> 1 <= results@[j] as int && results@[j] as int <= 1439,
        decreases test_cases.len() as int - i as int
    {
        let (h, m) = test_cases[i];
        let minutes = 1440i16 - ((h as i16 * 60) + m as i16);
        proof {
            let tc = test_cases@[i];
            assert(tc.0 >= 0 && tc.0 < 24 && tc.1 >= 0 && tc.1 < 60);
            let minutes_int = minutes_until_midnight(tc.0 as int, tc.1 as int);
            assert(minutes_int >= 1 && minutes_int <= 1439);
            assert(minutes as int == minutes_int);
        }
        results.push(minutes);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}