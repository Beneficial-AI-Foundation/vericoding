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
fn compute_sum_friends(friends: Vec<i8>) -> (s: i64)
    requires
        friends@.map_values(|x: i8| x as int).all(|x: int| 1 <= x <= 5),
    ensures
        s as int == sum_sequence(friends@.map_values(|x: i8| x as int)),
{
    let mut s: i64 = 0;
    let mut i: usize = 0;
    while i < friends.len()
        invariant
            0 <= i <= friends.len(),
            s as int == sum_sequence(friends@.map_values(|x: i8| x as int).subrange(0, i as int)),
        decreases friends.len() - i,
    {
        s = s + (friends@[i] as i64);
        i = i + 1;
    }
    s
}
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
    /* code modified by LLM (iteration 5): Updated to use executable types like i64 for sum, fingers, count, and total_people calculations to avoid ghost type errors; adjusted invariants and proofs to use converted types */
    let sum_friends: i64 = compute_sum_friends(friends);
    let total_people: i64 = (n as i64) + 1;
    let mut count: i64 = 0;
    let mut finger: i64 = 1;
    while finger <= 5
        invariant
            1 <= finger <= 6,
            count as int == count_valid_choices_helper(n as int, friends@.map_values(|x: i8| x as int), finger as int),
        decreases 6 - finger as int,
    {
        let total_sum: i64 = sum_friends + finger;
        if total_sum % total_people != 1 {
            proof { assert(!dima_cleans(n as int, friends@.map_values(|x: i8| x as int), finger as int)); }
            count = count + 1;
        } else {
            proof { assert(dima_cleans(n as int, friends@.map_values(|x: i8| x as int), finger as int)); }
        }
        finger = finger + 1;
    }
    count as i8
}
// </vc-code>


}

fn main() {}