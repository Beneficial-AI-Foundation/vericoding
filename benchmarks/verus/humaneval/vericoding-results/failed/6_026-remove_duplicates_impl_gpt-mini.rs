// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_frequency_spec(seq: Seq<i64>, key: i64) -> (result:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_spec(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): occurrence spec using count_frequency_spec */
spec fn occurs_once(numbers: &Vec<i64>, key: i64) -> bool {
    count_frequency_spec(numbers@, key) == 1
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)

    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and push elements that occur exactly once; maintain invariants linking res@ to prefix filter and inner cnt to count_frequency_spec */
    let mut res: Vec<i64> = Vec::new();
    let n: usize = numbers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == numbers.len(),
            res@ == numbers@.slice(0, i).filter(|y: i64| count_frequency_spec(numbers@, y) == 1),
        decreases n - i
    {
        let x: i64 = numbers[i];
        let mut j: usize = 0;
        let mut cnt: int = 0;
        while j < n
            invariant
                j <= n,
                n == numbers.len(),
                cnt == count_frequency_spec(numbers@.slice(0, j), x),
            decreases n - j
        {
            if numbers[j] == x {
                cnt = cnt + 1;
            }
            j = j + 1;
        }
        if cnt == 1 {
            res.push(x);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}