// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, friends: Seq<int>) -> bool {
  n >= 1 && friends.len() == n && forall|i: int| 0 <= i < friends.len() ==> #[trigger] friends[i] >= 1 && #[trigger] friends[i] <= 5
}

spec fn sum_sequence(s: Seq<int>) -> int
  decreases s.len()
{
  if s.len() == 0 { 0 } else { s[0] + sum_sequence(s.subrange(1, s.len() as int)) }
}

spec fn dima_cleans(n: int, friends: Seq<int>, dima_fingers: int) -> bool {
  &&& valid_input(n, friends)
  &&& 1 <= dima_fingers <= 5
  &&& {
    let total_sum = sum_sequence(friends) + dima_fingers;
    let total_people = n + 1;
    total_sum % total_people == 1
  }
}

spec fn count_valid_choices(n: int, friends: Seq<int>) -> int {
  if valid_input(n, friends) {
    count_valid_choices_helper(n, friends, 1)
  } else {
    0
  }
}

spec fn count_valid_choices_helper(n: int, friends: Seq<int>, finger_count: int) -> int
  decreases 6 - finger_count
{
  if !(valid_input(n, friends) && 1 <= finger_count <= 6) {
    0
  } else if finger_count > 5 {
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
fn solve(n: i8, friends: Vec<i8>) -> (result: i8)
  requires 
    valid_input(n as int, friends@.map_values(|x: i8| x as int))
  ensures 
    0 <= result <= 5,
    result as int == count_valid_choices(n as int, friends@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant blocks with curly braces */
    let mut total: i32 = 0;
    let mut i = 0;
    while i < friends.len()
        invariant {
            0 <= i <= friends.len(),
            0 <= total <= 5 * i,
        }
    {
        total += friends[i] as i32;
        i += 1;
    }

    let divisor = n as i32 + 1;
    proof {
        assert(divisor > 0);
    }

    let mut count: i32 = 0;
    let mut finger = 1;
    while finger <= 5
        invariant {
            1 <= finger <= 6,
            0 <= count <= finger - 1,
        }
        decreases 6 - finger
    {
        let sum = total + finger;
        if sum % divisor != 1 {
            count += 1;
        }
        finger += 1;
    }

    count as i8
}
// </vc-code>


}

fn main() {}