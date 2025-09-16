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
/* helper modified by LLM (iteration 3): predicate for uniqueness based on count_frequency_spec */
spec fn is_unique(seq: Seq<i64>, x: i64) -> bool { count_frequency_spec(seq, x) == 1 }

/* helper modified by LLM (iteration 3): filter-push lemma specialized to is_unique predicate */
proof fn lemma_filter_push_unique(s: Seq<i64>, full: Seq<i64>, x: i64)
    ensures
        s.push(x).filter(|y: i64| is_unique(full, y))
        == if is_unique(full, x) {
                s.filter(|y: i64| is_unique(full, y)).push(x)
           } else {
                s.filter(|y: i64| is_unique(full, y))
           }
{ }

/* helper modified by LLM (iteration 3): take-push relationship for sequences */
proof fn lemma_take_push_index<T>(s: Seq<T>, i: int)
    requires
        0 <= i,
        i < s.len() as int,
    ensures
        s.take(i + 1) == s.take(i).push(s[i])
{ }

/* helper modified by LLM (iteration 3): taking full length (as int) yields original sequence */
proof fn lemma_take_full<T>(s: Seq<T>)
    ensures
        s.take(s.len() as int) == s
{ }
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)

    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): filter unique elements by iterating once and preserving invariant */
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            result@ == numbers@.take(i as int).filter(|y: i64| is_unique(numbers@, y)),
            0 <= i as int,
            i as int <= numbers.len() as int,
        decreases numbers.len() as int - i as int
    {
        let x = numbers[i];
        if is_unique(numbers@, x) {
            result.push(x);
            proof {
                lemma_take_push_index::<i64>(numbers@, i as int);
                assert(numbers@[i as int] == x);
                lemma_filter_push_unique(numbers@.take(i as int), numbers@, x);
            }
        } else {
            proof {
                lemma_take_push_index::<i64>(numbers@, i as int);
                assert(numbers@[i as int] == x);
                lemma_filter_push_unique(numbers@.take(i as int), numbers@, x);
            }
        }
        i += 1;
    }
    proof {
        lemma_take_full::<i64>(numbers@);
    }
    result
}
// </vc-code>

}
fn main() {}