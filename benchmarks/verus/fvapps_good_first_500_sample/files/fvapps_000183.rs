// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_valid_digit_char(c: char) -> bool {
    c >= '1' && c <= '9'
}

spec fn char_to_digit(c: char) -> int {
    (c as int) - ('0' as int)
}

spec fn digit_cost_sum(s: Seq<char>, costs: Seq<nat>) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let digit = char_to_digit(s[0]);
        if 1 <= digit <= 9 && costs.len() == 9 {
            costs[digit - 1] + digit_cost_sum(s.skip(1), costs)
        } else {
            0
        }
    }
}

fn largest_number(costs: Vec<nat>, target: int) -> (result: String)
    requires 
        costs.len() == 9,
        forall|i: int| 0 <= i < 9 ==> #[trigger] costs[i] >= 1 && #[trigger] costs[i] <= 5000,
        1 <= target <= 5000,
    ensures
        result@.len() > 0,
        result@ == seq!['0'] || digit_cost_sum(result@, costs@) == target,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

}

fn main() {
    // let result1 = largest_number(vec![4, 3, 2, 5, 6, 7, 2, 5, 5], 9);
    // println!("{}", result1); // Expected: "7772"
    
    // let result2 = largest_number(vec![7, 6, 5, 5, 5, 6, 8, 7, 8], 12);
    // println!("{}", result2); // Expected: "85"
    
    // let result3 = largest_number(vec![2, 4, 6, 2, 4, 6, 4, 4, 4], 5);
    // println!("{}", result3); // Expected: "0"
}