// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, friends: Seq<int>) -> bool {
    n >= 1 && friends.len() == n && forall|i: int| 0 <= i < friends.len() ==> 1 <= friends[i] <= 5
}

spec fn sum_sequence(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_sequence(s.subrange(1, s.len() as int)) }
}

spec fn dima_cleans(n: int, friends: Seq<int>, dima_fingers: int) -> bool {
    let total_sum = sum_sequence(friends) + dima_fingers;
    let total_people = n + 1;
    total_sum % total_people == 1
}

spec fn count_valid_choices(n: int, friends: Seq<int>) -> int {
    count_valid_choices_helper(n, friends, 1)
}

spec fn count_valid_choices_helper(n: int, friends: Seq<int>, finger_count: int) -> int
    decreases 6 - finger_count
{
    if finger_count > 5 {
        0
    } else if !dima_cleans(n, friends, finger_count) {
        1 + count_valid_choices_helper(n, friends, finger_count + 1)
    } else {
        count_valid_choices_helper(n, friends, finger_count + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, friends: Seq<int>) -> (result: int)
    requires
        valid_input(n, friends)
    ensures
        0 <= result <= 5,
        result == count_valid_choices(n, friends)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}