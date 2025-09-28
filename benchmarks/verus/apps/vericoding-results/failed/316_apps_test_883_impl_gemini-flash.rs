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
/* helper modified by LLM (iteration 5): Removed `!` from lemma definition to fix compilation error. */
lemma fn lemma_sum_sequence_non_negative(s: Seq<int>)
  ensures sum_sequence(s) >= 0
  decreases s.len()
{
  if s.len() == 0 {
  } else {
    lemma_sum_sequence_non_negative(s.subrange(1, s.len() as int));
  }
}

spec fn count_fingers_where_dima_cleans_model(n: int, friends: Seq<int>, dima_fingers: int) -> bool {
  let total_sum = sum_sequence(friends) + dima_fingers;
  let total_people = n + 1;
  total_sum % total_people == 1
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
/* code modified by LLM (iteration 5): No functional change, removed comments */
{
    let n_int = n as int;
    let friends_seq = friends@.map_values(|x:i8| x as int);
    let mut count: i8 = 0;
    let mut dima_fingers_int: int = 1;

    while dima_fingers_int <= 5
      invariant
        1 <= dima_fingers_int <= 6,
        0 <= count,
        count as int == count_valid_choices(n_int, friends_seq) - count_valid_choices_helper(n_int, friends_seq, dima_fingers_int),
      decreases 6 - dima_fingers_int
    {
      if !dima_cleans(n_int, friends_seq, dima_fingers_int) {
        count = count + 1;
      }
      dima_fingers_int = dima_fingers_int + 1;
    }
    count
}
// </vc-code>


}

fn main() {}