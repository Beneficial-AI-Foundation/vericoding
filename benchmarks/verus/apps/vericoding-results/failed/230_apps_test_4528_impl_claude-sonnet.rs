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
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing duplicate lemma keyword */
proof fn lemma_minutes_until_midnight_bounds(h: int, m: int)
    requires
        h >= 0,
        h < 24,
        m >= 0,
        m < 60,
        !(h == 0 && m == 0)
    ensures
        1 <= minutes_until_midnight(h, m) <= 1439
{
    let total_minutes = h * 60 + m;
    assert(total_minutes >= 1);
    assert(total_minutes <= 23 * 60 + 59);
    assert(total_minutes <= 1439);
    assert(1440 - total_minutes >= 1);
    assert(1440 - total_minutes <= 1439);
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
    /* code modified by LLM (iteration 5): used ghost variables for int conversions */
    let mut results: Vec<i16> = Vec::new();
    let mut i = 0;
    
    while i < test_cases.len()
        invariant
            i <= test_cases.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] results[j] as int == minutes_until_midnight(test_cases[j].0 as int, test_cases[j].1 as int),
            valid_output(results@.map(|k: int, x: i16| x as int))
    {
        ghost let h = test_cases[i].0 as int;
        ghost let m = test_cases[i].1 as int;
        
        proof {
            lemma_minutes_until_midnight_bounds(h, m);
        }
        
        let total_minutes = test_cases[i].0 as i16 * 60 + test_cases[i].1 as i16;
        let result = 1440 - total_minutes;
        
        results.push(result);
        i += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}