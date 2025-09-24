// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn possible(n: int, food_types: Seq<int>, days: int) -> bool
    recommends n >= 0, days >= 0, forall|i: int| 0 <= i < food_types.len() ==> food_types[i] >= 1
{
    if days == 0 { true }
    else {
        let total_participants = count_total_participants(food_types, days, 1);
        total_participants >= n
    }
}

spec fn count_total_participants(food_types: Seq<int>, days: int, current_type: int) -> int
    recommends days >= 0, current_type >= 1
    decreases 101 - current_type
{
    if current_type > 100 { 0 }
    else {
        let packages_of_this_type = count_packages(food_types, current_type);
        let participants_for_this_type = if days > 0 { packages_of_this_type / days } else { 0 };
        participants_for_this_type + count_total_participants(food_types, days, current_type + 1)
    }
}

spec fn count_packages(food_types: Seq<int>, target_type: int) -> int
    recommends target_type >= 1
    decreases food_types.len()
{
    if food_types.len() == 0 { 0 }
    else if food_types[0] == target_type { 1 + count_packages(food_types.subrange(1, food_types.len() as int), target_type) }
    else { count_packages(food_types.subrange(1, food_types.len() as int), target_type) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, food_types: Vec<i8>) -> (result: i8)
    requires 1 <= n <= 100,
             1 <= m <= 100,
             food_types@.len() == m as int,
             forall|i: int| 0 <= i < food_types@.len() ==> #[trigger] food_types@[i] >= 1 && #[trigger] food_types@[i] <= 100
    ensures result >= 0,
            result <= m,
            result > 0 ==> possible(n as int, food_types@.map(|i, x: i8| x as int), result as int),
            !possible(n as int, food_types@.map(|i, x: i8| x as int), result as int + 1),
            forall|d: int| #[trigger] possible(n as int, food_types@.map(|i, x: i8| x as int), d) ==> d <= result as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}