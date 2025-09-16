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
/* helper modified by LLM (iteration 5): Fixed integer type in count_frequency_lemma spec and eliminated ghost type conflict */
proof fn count_frequency_lemma(seq: Seq<i64>, key: i64, i: nat)
    requires
        0 <= i <= seq.len(),
    ensures
        count_frequency_spec(seq, key) == count_frequency_spec(seq.subrange(0, i as int), key) + count_frequency_spec(seq.subrange(i as int, seq.len() as int), key),
    decreases seq.len() - i,
{
    if i < seq.len() {
        count_frequency_lemma(seq.drop_last(), key, i);
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)

    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed integer literal comparison issue by using proper ghost cast */
{
    let mut unique_numbers = Vec::new();
    let mut index: usize = 0;
    
    while index < numbers.len()
        invariant
            index <= numbers.len(),
            unique_numbers@ == numbers@.subrange(0, index as int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
    {
        let current = numbers[index];
        proof {
            let freq = count_frequency_spec(numbers@, current);
            assert(freq >= 0);
        }
        if count_frequency_spec(numbers@, current) == 1 {
            unique_numbers.push(current);
        }
        index = index + 1;
    }
    
    unique_numbers
}
// </vc-code>

}
fn main() {}