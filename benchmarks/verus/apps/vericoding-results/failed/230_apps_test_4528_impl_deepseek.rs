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
proof fn lemma_positive_minutes_until_midnight(h: int, m: int) 
    requires 
        h >= 0, 
        h < 24, 
        m >= 0, 
        m < 60, 
        !(h == 0 && m == 0)
    ensures 
        minutes_until_midnight(h, m) >= 1, 
        minutes_until_midnight(h, m) <= 1439
{
    let total = h * 60 + m;
    assert(total >= 0 && total < 24 * 60) by { 
        assert(total >= 0);
        assert(total < 24 * 60);
    }; // max total is 23*60 + 59 = 1439
    assert(total <= 1439) by {
        assert(24 * 60 == 1440);
        assert(total <= 23 * 60 + 59);
        assert(23 * 60 + 59 == 1439);
    };
    assert(1440 - total >= 1);
    assert(1440 - total <= 1439);
}

proof fn lemma_test_case_bounds(test_cases: Vec<(i8, i8)>, i: int)
    requires 
        valid_input(test_cases@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int))),
        0 <= i < test_cases.len()
    ensures 
        test_cases[i].0 as int >= 0,
        test_cases[i].0 as int < 24,
        test_cases[i].1 as int >= 0,
        test_cases[i].1 as int < 60,
        !(test_cases[i].0 as int == 0 && test_cases[i].1 as int == 0)
{
    assert(test_cases@.index(i).0 >= 0 && test_cases@.index(i).0 < 24);
    assert(test_cases@.index(i).1 >= 0 && test_cases@.index(i).1 < 60);
    assert(!(test_cases@.index(i).0 == 0 && test_cases@.index(i).1 == 0));
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
    /* code modified by LLM (iteration 5): fixed bounds checking and lemma usage */
    let mut results = Vec::new();
    let len = test_cases.len();
    let mut i = 0;
    while i < len
        invariant 
            i <= len, 
            results.len() == i as nat, 
            forall|j: int| 0 <= j < i ==> 
                #[trigger] results@[j] as int == minutes_until_midnight(test_cases[j].0 as int, test_cases[j].1 as int), 
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] results@[j] as int && results@[j] as int <= 1439
        decreases 
            len - i
    {
        proof {
            lemma_test_case_bounds(test_cases, i);
            assert(0 <= i && i < test_cases.len());
        }
        let (h, m) = test_cases[i];
        proof {
            lemma_positive_minutes_until_midnight(h as int, m as int);
        }
        let h_i32 = h as i32;
        let m_i32 = m as i32;
        let total_minutes_before_midnight = 1440 - (h_i32 * 60 + m_i32);
        let result = total_minutes_before_midnight as i16;
        assert(result as int == minutes_until_midnight(h as int, m as int));
        results.push(result);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}