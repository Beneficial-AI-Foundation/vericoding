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
/* helper modified by LLM (iteration 5): Fix compilation error by removing 'ghost' keyword from fn sum_sequence_intseq and using proper spec function */
spec fn lemma_count_valid_choices_helper_range(n: int, friends: Seq<int>, start: int)
    requires
        valid_input(n, friends),
        1 <= start <= 6,
    ensures
        forall|f: int| start <= f <= 5 ==> (dima_cleans(n, friends, f) || !dima_cleans(n, friends, f)),
        count_valid_choices_helper(n, friends, start) <= 5 - start + 1,
        count_valid_choices_helper(n, friends, start) >= 0,
    decreases 6 - start
{
    if start <= 5 {
        lemma_count_valid_choices_helper_range(n, friends, start + 1);
    }
}

proof fn lemma_dima_cleans_mod_1(n: int, friends: Seq<int>, fingers: int)
    requires
        valid_input(n, friends),
        1 <= fingers <= 5,
    ensures
        dima_cleans(n, friends, fingers) == ((sum_sequence(friends) + fingers) % (n + 1) == 1)
{
}

proof fn lemma_valid_input_preserved(n: int, friends: Seq<int>)
    requires
        valid_input(n, friends),
    ensures
        forall|f: int| 1 <= f <= 5 ==> valid_input(n, friends)
{
}

spec fn sum_sequence_intseq(s: Seq<int>) -> int
    ensures
        result == sum_sequence(s)
{
    if s.len() == 0 {
        0
    } else {
        sum_sequence_intseq(s.subrange(1, s.len())) + s[0]
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
    /* code modified by LLM (iteration 5): Fix implementation to properly calculate valid choices count using if condition */
    let ghost seq_friends = friends@.map_values(|x: i8| x as int);
    let ghost total_sum = sum_sequence_intseq(seq_friends);
    let ghost total_people = n as int + 1;
    let mut count: i8 = 0;
    let mut finger_count: i8 = 1;
    
    while finger_count <= 5
        invariant
            finger_count >= 1,
            finger_count <= 6,
            count as int == count_valid_choices_helper(n as int, seq_friends, finger_count as int),
        decreases 6 - (finger_count as int)
    {
        proof {
            lemma_dima_cleans_mod_1(n as int, seq_friends, finger_count as int);
        }
        
        if (total_sum + finger_count as int) % total_people != 1 {
            count = count + 1;
        }
        
        finger_count = finger_count + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}