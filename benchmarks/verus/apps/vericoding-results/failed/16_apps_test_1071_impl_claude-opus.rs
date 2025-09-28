// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>, b: Seq<int>, n: int) -> bool {
    a.len() >= 0 && b.len() >= 0 &&
    (forall|i: int| 0 <= i < a.len() ==> a[i] >= 0) &&
    (forall|j: int| 0 <= j < b.len() ==> b[j] >= 0) &&
    n >= 1
}

spec fn sum_seq(s: Seq<int>) -> int
    recommends forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.drop_first()) }
}

spec fn shelves_needed(total: int, capacity: int) -> int
    recommends capacity > 0
{
    if total == 0 { 0 } else { (total - 1) / capacity + 1 }
}

spec fn can_place_all(a: Seq<int>, b: Seq<int>, n: int) -> bool
    recommends valid_input(a, b, n)
{
    let total_cups = sum_seq(a);
    let total_medals = sum_seq(b);
    let shelves_for_cups = shelves_needed(total_cups, 5);
    let shelves_for_medals = shelves_needed(total_medals, 10);
    shelves_for_cups + shelves_for_medals <= n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed to helpers */
proof fn sum_seq_bounds(s: Seq<int>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    ensures
        sum_seq(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        sum_seq_bounds(s.drop_first());
    }
}

proof fn shelves_needed_correct(total: int, capacity: int)
    requires
        capacity > 0,
        total >= 0
    ensures
        shelves_needed(total, capacity) >= 0,
        shelves_needed(total, capacity) * capacity >= total,
        total > 0 ==> shelves_needed(total, capacity) > 0
{
    if total == 0 {
    } else {
        assert((total - 1) / capacity >= 0);
        assert((total - 1) / capacity + 1 > 0);
        assert(((total - 1) / capacity + 1) * capacity >= total);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>, b: Vec<i8>, n: i8) -> (result: String)
    requires valid_input(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int)
    ensures result@ == (if can_place_all(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int) { "YES"@ } else { "NO"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using String::new() for string creation */
    let mut cup_sum: i32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            cup_sum >= 0,
            cup_sum == sum_seq(a@.map(|j: int, x: i8| x as int).take(i as int)) as int
    {
        proof {
            assert(a@.map(|j: int, x: i8| x as int).take((i + 1) as int) =~= 
                   a@.map(|j: int, x: i8| x as int).take(i as int).push(a[i as int] as int));
        }
        cup_sum = cup_sum + (a[i] as i32);
        i = i + 1;
    }
    
    proof {
        assert(a@.map(|j: int, x: i8| x as int).take(a.len() as int) =~= a@.map(|j: int, x: i8| x as int));
        sum_seq_bounds(a@.map(|j: int, x: i8| x as int));
    }
    
    let mut medal_sum: i32 = 0;
    let mut j: usize = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            medal_sum >= 0,
            medal_sum == sum_seq(b@.map(|k: int, x: i8| x as int).take(j as int)) as int
    {
        proof {
            assert(b@.map(|k: int, x: i8| x as int).take((j + 1) as int) =~= 
                   b@.map(|k: int, x: i8| x as int).take(j as int).push(b[j as int] as int));
        }
        medal_sum = medal_sum + (b[j] as i32);
        j = j + 1;
    }
    
    proof {
        assert(b@.map(|k: int, x: i8| x as int).take(b.len() as int) =~= b@.map(|k: int, x: i8| x as int));
        sum_seq_bounds(b@.map(|k: int, x: i8| x as int));
    }
    
    let shelves_for_cups: i32 = if cup_sum == 0 { 0 } else { (cup_sum - 1) / 5 + 1 };
    let shelves_for_medals: i32 = if medal_sum == 0 { 0 } else { (medal_sum - 1) / 10 + 1 };
    
    proof {
        shelves_needed_correct(cup_sum as int, 5);
        shelves_needed_correct(medal_sum as int, 10);
        assert(shelves_for_cups == shelves_needed(cup_sum as int, 5));
        assert(shelves_for_medals == shelves_needed(medal_sum as int, 10));
    }
    
    if shelves_for_cups + shelves_for_medals <= (n as i32) {
        String::new("YES")
    } else {
        String::new("NO")
    }
}
// </vc-code>


}

fn main() {}