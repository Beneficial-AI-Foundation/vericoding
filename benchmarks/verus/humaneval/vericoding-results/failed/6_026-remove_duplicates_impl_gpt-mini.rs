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
/* helper modified by LLM (iteration 5): helper to check if an element occurs exactly once in a sequence */
spec fn is_single(seq: Seq<i64>, x: i64) -> bool { count_frequency_spec(seq, x) == 1 }
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)

    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): loop with proper decreases and invariants to build filtered vector */
    let mut res: Vec<i64> = Vec::new();
    let n: usize = numbers.len();
    let mut i: usize = 0usize;
    while i < n
        invariant
            i <= n,
            res@ == numbers@.take(i).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
        decreases n - i
    {
        let v: i64 = numbers[i];
        let mut count: int = 0;
        let mut j: usize = 0usize;
        while j < n
            invariant
                j <= n,
                count == count_frequency_spec(numbers@.take(j), v),
            decreases n - j
        {
            if numbers[j] == v {
                count = count + 1;
            }
            j += 1usize;
        }
        if count == 1 {
            res.push(v);
        }
        i += 1usize;
    }
    res
}
// </vc-code>

}
fn main() {}