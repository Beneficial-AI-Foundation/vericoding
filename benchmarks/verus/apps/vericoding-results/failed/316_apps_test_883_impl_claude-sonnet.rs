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
/* helper modified by LLM (iteration 5): fixed trigger annotations */
proof fn sum_sequence_distributive(s1: Seq<int>, s2: Seq<int>)
    ensures sum_sequence(s1.add(s2)) == sum_sequence(s1) + sum_sequence(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1.add(s2) == s2);
    } else {
        let s1_tail = s1.subrange(1, s1.len() as int);
        sum_sequence_distributive(s1_tail, s2);
        assert(s1.add(s2)[0] == s1[0]);
        assert(s1.add(s2).subrange(1, (s1.add(s2)).len() as int) == s1_tail.add(s2));
    }
}

fn compute_sum_i8(friends: &Vec<i8>) -> (sum: i32)
    requires 
        friends@.len() >= 1,
        forall|i: int| 0 <= i < friends@.len() ==> #[trigger] friends@[i] >= 1 && #[trigger] friends@[i] <= 5
    ensures 
        sum as int == sum_sequence(friends@.map_values(|x: i8| x as int)),
        0 <= sum <= 5 * friends@.len()
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < friends.len()
        invariant
            0 <= i <= friends.len(),
            sum as int == sum_sequence(friends@.subrange(0, i as int).map_values(|x: i8| x as int)),
            0 <= sum <= 5 * i
        decreases friends.len() - i
    {
        sum = sum + friends[i] as i32;
        i = i + 1;
    }
    
    sum
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
    /* code modified by LLM (iteration 5): fixed loop invariant and implementation */
    let friends_sum = compute_sum_i8(&friends);
    let total_people = n as i32 + 1;
    let mut count: i8 = 0;
    let mut finger_count: i8 = 1;
    
    while finger_count <= 5
        invariant
            1 <= finger_count <= 6,
            0 <= count <= 5,
            count as int == count_valid_choices_helper(n as int, friends@.map_values(|x: i8| x as int), 1) - count_valid_choices_helper(n as int, friends@.map_values(|x: i8| x as int), finger_count as int)
        decreases 5 - finger_count
    {
        let total_sum = friends_sum + finger_count as i32;
        let remainder = total_sum % total_people;
        
        if remainder != 1 {
            count = count + 1;
        }
        
        finger_count = finger_count + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}