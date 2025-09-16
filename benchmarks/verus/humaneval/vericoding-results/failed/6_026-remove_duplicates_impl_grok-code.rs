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

// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)

    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type errors and casting issues in while loop, using int for j and proper indexing */
    let mut result = Vec::new();
    let tracked mut j: int = 0;
    proof {
        j = 0;
    }
    while j < (numbers@.len() as int)
        invariant
            j >= 0,
            j <= (numbers@.len() as int),
            result@ == numbers@.take(j as int).filter(|x: i64| count_frequency_spec(numbers@, x) == (1 as int)),
        decreases (numbers@.len() as int) - j
    {
        let num = numbers@[j as int];
        let checked = count_frequency_spec(numbers@, num) == (1 as int);
        if checked {
            result.push(num);
        }
        proof {
            j = j + 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}