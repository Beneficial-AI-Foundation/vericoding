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
/* helper modified by LLM (iteration 5): Added helper lemmas for sum operations */
proof fn sum_empty()
    ensures sum(Seq::<int>::empty()) == 0
{
}

proof fn sum_singleton(x: int)
    ensures sum(seq![x]) == x
{
    assert(seq![x].subrange(1, 1) =~= Seq::<int>::empty());
}

proof fn sum_push(s: Seq<int>, x: int)
    ensures sum(s.push(x)) == sum(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        sum_singleton(x);
    } else {
        assert(s.push(x).subrange(1, (s.len() + 1) as int) =~= s.subrange(1, s.len() as int).push(x));
        sum_push(s.subrange(1, s.len() as int), x);
    }
}

proof fn sum_subrange_split(s: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len(),
    ensures
        sum(s.subrange(i, k)) == sum(s.subrange(i, j)) + sum(s.subrange(j, k))
    decreases k - i
{
    if i == k {
        assert(s.subrange(i, j) =~= Seq::<int>::empty());
        assert(s.subrange(j, k) =~= Seq::<int>::empty());
    } else if i == j {
        assert(s.subrange(i, j) =~= Seq::<int>::empty());
    } else {
        assert(s.subrange(i, k).subrange(1, (k - i) as int) =~= s.subrange(i + 1, k));
        assert(s.subrange(i, j).subrange(1, (j - i) as int) =~= s.subrange(i + 1, j));
        sum_subrange_split(s, i + 1, j, k);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: (i8, Vec<i8>))
    requires valid_input(n as int, k as int, a@.map_values(|x: i8| x as int))
    ensures valid_output(a@.map_values(|x: i8| x as int), result.1@.map_values(|x: i8| x as int), result.0 as int, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added trigger annotations to forall quantifiers in invariants */
    let mut schedule = Vec::<i8>::new();
    let mut total_added = 0i8;
    let mut i = 0i8;
    
    while i < n
        invariant
            0 <= i <= n,
            schedule.len() == i as int,
            total_added >= 0,
            total_added as int == sum(schedule@.map_values(|x: i8| x as int)) - sum(a@.subrange(0, i as int).map_values(|x: i8| x as int)),
            forall|j: int| 0 <= j < i ==> #[trigger] schedule[j as int] as int >= a[j as int] as int,
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] (schedule[j as int] as int + schedule[(j + 1) as int] as int) >= k as int,
        decreases n - i
    {
        let current_walks = a[i as usize];
        let mut needed_walks = current_walks;
        
        if i > 0 {
            let prev_walks = schedule[(i - 1) as usize];
            if prev_walks + current_walks < k {
                let deficit = k - prev_walks - current_walks;
                needed_walks = current_walks + deficit;
            }
        }
        
        schedule.push(needed_walks);
        total_added = total_added + (needed_walks - current_walks);
        
        proof {
            assert(schedule@.subrange(0, i as int) =~= schedule@.take(i as int));
            if i > 0 {
                assert(schedule[(i - 1) as int] as int + schedule[i as int] as int >= k as int);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(a@.subrange(0, n as int) =~= a@);
        assert(forall|j: int| 0 <= j < n ==> #[trigger] schedule[j as int] as int >= a[j as int] as int);
        assert(forall|j: int| 0 <= j < n - 1 ==> #[trigger] (schedule[j as int] as int + schedule[(j + 1) as int] as int) >= k as int);
    }
    
    (total_added, schedule)
}
// </vc-code>


}

fn main() {}