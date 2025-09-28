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
/* helper modified by LLM (iteration 5): compute sum of valid choices from a starting finger to 5 */
spec fn sum_from(finger: int, n: int, friends: Seq<int>) -> int
  decreases 6 - finger
{
  if finger > 5 as int { 0 as int } else { (if !dima_cleans(n, friends, finger) { 1 as int } else { 0 as int }) + sum_from(finger + 1, n, friends) }
}

/* helper modified by LLM (iteration 5): lemma linking count_valid_choices_helper to the explicit sum_from function */
fn count_helper_correct(n: int, friends: Seq<int>, finger: int)
  requires
    valid_input(n, friends),
    1 <= finger <= 6,
  ensures
    count_valid_choices_helper(n, friends, finger) == sum_from(finger, n, friends),
  decreases
    6 - finger
{
  if finger > 5 as int {
    proof {
      assert(count_valid_choices_helper(n, friends, finger) == 0 as int);
      assert(sum_from(finger, n, friends) == 0 as int);
    }
  } else {
    proof {
      count_helper_correct(n, friends, finger + 1);
      if !dima_cleans(n, friends, finger) {
        assert(count_valid_choices_helper(n, friends, finger) == 1 as int + count_valid_choices_helper(n, friends, finger + 1));
        assert(sum_from(finger, n, friends) == 1 as int + sum_from(finger + 1, n, friends));
        assert(count_valid_choices_helper(n, friends, finger + 1) == sum_from(finger + 1, n, friends));
      } else {
        assert(count_valid_choices_helper(n, friends, finger) == count_valid_choices_helper(n, friends, finger + 1));
        assert(sum_from(finger, n, friends) == sum_from(finger + 1, n, friends));
        assert(count_valid_choices_helper(n, friends, finger + 1) == sum_from(finger + 1, n, friends));
      }
    }
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
  /* code modified by LLM (iteration 5): compute runtime count and prove equality with spec count */
  let tracked n_int: int = n as int;
  let tracked friends_seq: Seq<int> = friends@.map_values(|x: i8| x as int);

  // compute runtime sum of friends into runtime_sum, maintain equality with spec prefix sums
  let mut runtime_sum: int = 0 as int;
  let mut i: int = 0 as int;
  while i < friends.len() as int
      invariant
          0 <= i && i <= friends.len() as int,
          runtime_sum == sum_sequence(friends_seq.subrange(0, i)),
      decreases friends.len() as int - i
  {
    runtime_sum = runtime_sum + (friends[i as usize] as int);
    i = i + 1;
  }

  // count fingers at runtime
  let mut cnt: i8 = 0i8;
  let mut finger: int = 1 as int;
  while finger <= 5 as int
      invariant
          0 <= cnt as int && cnt as int <= 5,
          1 <= finger && finger <= 6,
      decreases 6 - finger
  {
    let total_sum = runtime_sum + finger;
    let total_people = n_int + 1 as int;
    if total_sum % total_people != 1 as int {
      cnt = cnt + 1i8;
    }
    finger = finger + 1;
  }

  // proof: relate runtime computation to spec definitions
  proof {
    // runtime_sum equals the full spec sum
    assert(runtime_sum == sum_sequence(friends_seq));

    // show that for every finger the runtime condition matches the spec predicate
    let mut f: int = 1 as int;
    while f <= 5 as int
        invariant
            1 <= f && f <= 6,
        decreases 6 - f
    {
      assert(((runtime_sum + f) % (n_int + 1 as int) == 1 as int) == dima_cleans(n_int, friends_seq, f));
      f = f + 1;
    }

    // prove that the runtime count equals sum_from(1, ...)
    let mut acc: int = 0 as int;
    let mut f2: int = 1 as int;
    while f2 <= 5 as int
        invariant
            1 <= f2 && f2 <= 6,
            acc + sum_from(f2, n_int, friends_seq) == sum_from(1 as int, n_int, friends_seq),
        decreases 6 - f2
    {
      // the equivalence between runtime test and dima_cleans lets us update acc accordingly
      assert(((runtime_sum + f2) % (n_int + 1 as int) == 1 as int) == dima_cleans(n_int, friends_seq, f2));
      if (runtime_sum + f2) % (n_int + 1 as int) != 1 as int {
        // runtime says Dima does NOT clean -> contributes 1
        acc = acc + 1 as int;
        assert(!dima_cleans(n_int, friends_seq, f2));
        assert(sum_from(f2, n_int, friends_seq) == 1 as int + sum_from(f2 + 1 as int, n_int, friends_seq));
      } else {
        // runtime says Dima cleans -> contributes 0
        assert(dima_cleans(n_int, friends_seq, f2));
        assert(sum_from(f2, n_int, friends_seq) == sum_from(f2 + 1 as int, n_int, friends_seq));
      }
      // from the above, acc + sum_from(f2 + 1, ...) == previous acc + (if !dima then 1 else 0) + sum_from(f2 + 1, ...) == sum_from(1,...)
      f2 = f2 + 1;
    }
    assert(acc == sum_from(1 as int, n_int, friends_seq));

    // runtime cnt equals acc
    assert((cnt as int) == acc);

    // connect sum_from to count_valid_choices via lemma
    count_helper_correct(n_int, friends_seq, 1 as int);
    assert((cnt as int) == count_valid_choices(n_int, friends_seq));
  }

  cnt
}

// </vc-code>


}

fn main() {}