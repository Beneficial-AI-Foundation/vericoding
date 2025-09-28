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
/* helper modified by LLM (iteration 5): Added sum computation helper and retained proof helpers */
fn compute_sum(friends: &Vec<i8>) -> (sum: i32)
    ensures
        sum == friends@.fold_left(0i32, |acc: i32, x: i8| acc + x as i32)
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < friends.len()
        invariant
            0 <= i <= friends.len(),
            sum == friends@.subrange(0, i as int).fold_left(0i32, |acc: i32, x: i8| acc + x as i32)
    {
        sum = sum + friends[i] as i32;
        i = i + 1;
    }
    sum
}

proof fn sum_sequence_bounds(s: Seq<int>)
    requires
        forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 5
    ensures
        s.len() <= sum_sequence(s) <= 5 * s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        sum_sequence_bounds(s.subrange(1, s.len() as int));
    }
}

proof fn count_valid_choices_helper_bounds(n: int, friends: Seq<int>, finger_count: int)
    requires
        valid_input(n, friends),
        1 <= finger_count <= 6
    ensures
        0 <= count_valid_choices_helper(n, friends, finger_count) <= 6 - finger_count
    decreases 6 - finger_count
{
    if finger_count > 5 {
    } else {
        count_valid_choices_helper_bounds(n, friends, finger_count + 1);
    }
}

proof fn sum_fold_equals_sum_sequence(friends: Seq<i8>)
    ensures
        friends.fold_left(0i32, |acc: i32, x: i8| acc + x as i32) as int ==
        sum_sequence(friends.map_values(|x: i8| x as int))
    decreases friends.len()
{
    if friends.len() == 0 {
    } else {
        let tail = friends.subrange(1, friends.len() as int);
        sum_fold_equals_sum_sequence(tail);
        assert(friends.fold_left(0i32, |acc: i32, x: i8| acc + x as i32) ==
               friends[0] as i32 + tail.fold_left(0i32, |acc: i32, x: i8| acc + x as i32));
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
    /* code modified by LLM (iteration 5): Use compute_sum helper to avoid unsupported fold */
    let mut count: i8 = 0;
    let mut finger: i8 = 1;
    let friends_sum: i32 = compute_sum(&friends);
    let total_people = (n + 1) as i32;
    
    proof {
        let friends_int = friends@.map_values(|x: i8| x as int);
        sum_sequence_bounds(friends_int);
        sum_fold_equals_sum_sequence(friends@);
        assert(friends_sum as int == sum_sequence(friends_int));
    }
    
    while finger <= 5
        invariant
            1 <= finger <= 6,
            0 <= count <= 5,
            n >= 1,
            friends@.len() == n,
            friends_sum as int == sum_sequence(friends@.map_values(|x: i8| x as int)),
            total_people == n + 1,
            count as int == count_valid_choices_helper(n as int, friends@.map_values(|x: i8| x as int), 1) - 
                           count_valid_choices_helper(n as int, friends@.map_values(|x: i8| x as int), finger as int)
    {
        let total_sum = friends_sum + finger as i32;
        if total_sum % total_people != 1 {
            count = count + 1;
        }
        
        proof {
            let friends_int = friends@.map_values(|x: i8| x as int);
            assert(if !dima_cleans(n as int, friends_int, finger as int) {
                count_valid_choices_helper(n as int, friends_int, finger as int) ==
                1 + count_valid_choices_helper(n as int, friends_int, (finger + 1) as int)
            } else {
                count_valid_choices_helper(n as int, friends_int, finger as int) ==
                count_valid_choices_helper(n as int, friends_int, (finger + 1) as int)
            });
        }
        
        finger = finger + 1;
    }
    
    proof {
        let friends_int = friends@.map_values(|x: i8| x as int);
        assert(count_valid_choices_helper(n as int, friends_int, 6) == 0);
        assert(count as int == count_valid_choices_helper(n as int, friends_int, 1));
        assert(count as int == count_valid_choices(n as int, friends_int));
        count_valid_choices_helper_bounds(n as int, friends_int, 1);
    }
    
    count
}
// </vc-code>


}

fn main() {}