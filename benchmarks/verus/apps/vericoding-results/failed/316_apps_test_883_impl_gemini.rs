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
proof fn sum_sequence_append(s: Seq<int>, x: int)
    ensures sum_sequence(s.push(x)) == sum_sequence(s) + x
    decreases s.len()
{
    if s.len() > 0 {
        assert(s.push(x).subrange(1, s.len() + 1) == s.subrange(1, s.len()).push(x));
        sum_sequence_append(s.subrange(1, s.len()), x);
    }
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
    /* code modified by LLM (iteration 2): fixed compilation errors and strengthened an invariant for range checking */
    let ghost friends_seq = friends@.map_values(|x: i8| x as int);

    let mut friends_sum: i32 = 0;
    let mut i: i32 = 0;
    while i < n as i32
        invariant
            valid_input(n as int, friends_seq),
            0 <= i <= n as int,
            friends_sum as int == sum_sequence(friends_seq.subrange(0, i as int)),
        decreases (n as int) - i
    {
        proof {
            let sub_seq = friends_seq.subrange(0, i as int);
            let next_elem = friends_seq[i as int];
            assert(friends_seq.subrange(0, (i + 1) as int) === sub_seq.push(next_elem));
            sum_sequence_append(sub_seq, next_elem);
        }
        
        friends_sum = friends_sum + friends[i as usize] as i32;
        i = i + 1;
    }

    let mut valid_ways: i8 = 0;
    let mut dima_fingers: i8 = 1;
    while dima_fingers <= 5
        invariant
            1 <= dima_fingers <= 6,
            0 <= valid_ways <= dima_fingers - 1,
            valid_input(n as int, friends_seq),
            friends_sum as int == sum_sequence(friends_seq),
            count_valid_choices(n as int, friends_seq) == (valid_ways as int)
                + count_valid_choices_helper(n as int, friends_seq, dima_fingers as int),
        decreases 6 - dima_fingers
    {
        let total_sum = friends_sum + (dima_fingers as i32);
        let total_people = (n as i32) + 1;

        proof {
            vstd::arithmetic::div_mod::lemma_rem_is_mod(total_sum as int, total_people as int);
        }

        if total_sum % total_people != 1 {
            valid_ways = valid_ways + 1;
        }
        
        dima_fingers = dima_fingers + 1;
    }

    return valid_ways;
}

// </vc-code>


}

fn main() {}