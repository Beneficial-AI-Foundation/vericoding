// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn possible(n: int, food_types: Seq<int>, days: int) -> bool {
    if days == 0 { 
        true 
    } else {
        let total_participants = count_total_participants(food_types, days, 1);
        total_participants >= n
    }
}

spec fn count_total_participants(food_types: Seq<int>, days: int, current_type: int) -> int 
    decreases 101 - current_type
{
    if current_type > 100 { 
        0 
    } else {
        let packages_of_this_type = count_packages(food_types, current_type);
        let participants_for_this_type = if days > 0 { packages_of_this_type / days } else { 0 };
        participants_for_this_type + count_total_participants(food_types, days, current_type + 1)
    }
}

spec fn count_packages(food_types: Seq<int>, target_type: int) -> int {
    if food_types.len() == 0 { 
        0 
    } else if food_types[0] == target_type { 
        1 + count_packages(food_types.subrange(1, food_types.len() as int), target_type) 
    } else { 
        count_packages(food_types.subrange(1, food_types.len() as int), target_type) 
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, food_types: Seq<int>) -> (result: int)
    requires 1 <= n && n <= 100,
    requires 1 <= m && m <= 100,
    requires food_types.len() == m,
    requires forall|i: int| 0 <= i < food_types.len() ==> 1 <= food_types[i] && food_types[i] <= 100,
    ensures result >= 0,
    ensures result <= m,
    ensures result > 0 ==> possible(n, food_types, result),
    ensures !possible(n, food_types, result + 1),
    ensures forall|d: int| d > result ==> !possible(n, food_types, d),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}