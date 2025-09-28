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
/* helper modified by LLM (iteration 5): compute minutes until midnight using int arithmetic and return i16 */
fn compute_minutes(h: i8, m: i8) -> i16
    ensures
        result as int == minutes_until_midnight(h as int, m as int),
{
    let hh: int = h as int;
    let mm: int = m as int;
    let total: int = hh * 60 + mm;
    let v: int = 1440 - total;
    v as i16
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
    /* code modified by LLM (iteration 5): iterate over test_cases, compute minutes and push into results */
    let mut results: Vec<i16> = Vec::new();
    results.reserve(test_cases.len());
    let mut i: usize = 0;
    while i < test_cases.len()
        invariant
            results.len() == i,
            forall|j: int| 0 <= j < results.len() as int ==> 
                #[trigger] results[j] as int == minutes_until_midnight(test_cases[j].0 as int, test_cases[j].1 as int),
        decreases test_cases.len() as int - i as int
    {
        let (h, m) = test_cases[i];
        let r = compute_minutes(h, m);
        results.push(r);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}