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
/* helper modified by LLM (iteration 5): added exec version of as_int_seq */
fn as_int_seq(s: Seq<i8>) -> Seq<int>
{
    s.map(|idx: int, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: (i8, Vec<i8>))
    requires valid_input(n as int, k as int, a@.map_values(|x: i8| x as int))
    ensures valid_output(a@.map_values(|x: i8| x as int), result.1@.map_values(|x: i8| x as int), result.0 as int, k as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented the solving logic */
{
    let mut schedule: Vec<i8> = a.clone();
    let a_int: Seq<int> = as_int_seq(a@);
    let mut schedule_int: Ghost<Seq<int>> = Ghost(as_int_seq(schedule@));
    let mut additional: i8 = 0;
    let mut i: usize = 0;
    while i < (n as usize - 1)
        invariant
            0 <= i < n as usize,
            schedule.len() == a.len(),
            schedule_int@.len() == a.len(),
            forall|j: int| 0 <= j < i ==> schedule_int@[j] + schedule_int@[j + 1] >= k as int,
            forall|j: int| 0 <= j < schedule.len() ==> #[trigger] schedule_int@[j] >= a_int[j],
            additional as int >= 0 && additional as int == sum(schedule_int@) - sum(a_int)
        decreases n as usize - i
    {
        proof {
            assert(forall|j: int| 0 <= j < i ==> schedule_int@[j] + schedule_int@[j + 1] >= k as int);
            assert(forall|j: int| 0 <= j < schedule.len() ==> schedule_int@[j] >= a_int[j]);
        }
        let current_sum_int: i16 = schedule[i] as i16 + schedule[i + 1] as i16;
        if current_sum_int < k as i16 {
            let deficit: i8 = (k as i16 - current_sum_int) as i8;
            assert(deficit <= i8::MAX - schedule[i + 1]);
            schedule.set(i + 1, schedule[i + 1] + deficit);
            additional += deficit;
            proof {
                let index_int = (i + 1) as int;
                let current_value_int = schedule_int@.index(index_int);
                let deficit_int = deficit as int;
                let new_value_int = current_value_int + deficit_int;
                let new_sch_int = schedule_int@.update(index_int, new_value_int);
                schedule_int = Ghost(new_sch_int);
            }
        }
        i += 1;
    }
    (additional, schedule)
}
// </vc-code>


}

fn main() {}