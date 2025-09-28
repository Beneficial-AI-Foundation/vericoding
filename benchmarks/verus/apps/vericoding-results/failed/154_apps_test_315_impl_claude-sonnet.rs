// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}

spec fn valid_input(n: int, k: int, a: Seq<int>) -> bool
{
    n >= 1 && a.len() == n && k >= 0 && forall|i: int| 0 <= i < n ==> #[trigger] a[i] >= 0
}

spec fn valid_output(a: Seq<int>, final_schedule: Seq<int>, additional_walks: int, k: int) -> bool
{
    final_schedule.len() == a.len() &&
    additional_walks >= 0 &&
    forall|i: int| 0 <= i < a.len() ==> #[trigger] final_schedule[i] >= a[i] &&
    forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] final_schedule[i] + final_schedule[i + 1] >= k &&
    additional_walks == sum(final_schedule) - sum(a)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added trigger annotation to lemma */
spec fn min(a: int, b: int) -> int
{
    if a <= b { a } else { b }
}

spec fn max(a: int, b: int) -> int
{
    if a >= b { a } else { b }
}

proof fn lemma_sum_update(s: Seq<int>, i: int, new_val: int)
    requires
        0 <= i < s.len(),
        new_val >= s[i]
    ensures
        sum(s.update(i, new_val)) == sum(s) + (new_val - s[i])
    decreases s.len()
{
    if i == 0 {
        if s.len() == 1 {
            assert(s.update(0, new_val) =~= seq![new_val]);
        } else {
            assert(s.update(0, new_val) =~= seq![new_val].add(s.subrange(1, s.len() as int)));
        }
    } else {
        lemma_sum_update(s.subrange(1, s.len() as int), i - 1, new_val);
    }
}

proof fn lemma_sum_non_negative(s: Seq<int>)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    ensures sum(s) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        lemma_sum_non_negative(s.subrange(1, s.len() as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: (i8, Vec<i8>))
    requires valid_input(n as int, k as int, a@.map_values(|x: i8| x as int))
    ensures valid_output(a@.map_values(|x: i8| x as int), result.1@.map_values(|x: i8| x as int), result.0 as int, k as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added trigger annotation to invariant */
{
    let mut schedule = a.clone();
    let mut total_added = 0i8;
    
    let mut i = 0usize;
    while i < (n - 1) as usize
        invariant
            0 <= i <= (n - 1) as usize,
            schedule.len() == n,
            forall|j: int| 0 <= j < schedule.len() ==> #[trigger] schedule[j] >= a[j],
            forall|j: int| 0 <= j < i as int ==> #[trigger] (schedule[j] + schedule[j + 1]) >= k,
            total_added >= 0,
            total_added as int == sum(schedule@.map_values(|x: i8| x as int)) - sum(a@.map_values(|x: i8| x as int))
        decreases (n - 1) as usize - i
    {
        if schedule[i] + schedule[i + 1] < k {
            let needed = k - schedule[i] - schedule[i + 1];
            proof {
                lemma_sum_update(schedule@.map_values(|x: i8| x as int), (i + 1) as int, (schedule[i + 1] + needed) as int);
            }
            schedule.set(i + 1, schedule[i + 1] + needed);
            total_added = total_added + needed;
        }
        i = i + 1;
    }
    
    (total_added, schedule)
}
// </vc-code>


}

fn main() {}