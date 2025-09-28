use vstd::prelude::*;

verus! {

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
spec fn min_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let min_prefix = min_seq(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let max_prefix = max_seq(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}

// <vc-helpers>
spec fn min_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len()
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        proof { assert(prefix.len() < a.len()); }
        let min_prefix = min_seq(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len()
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        proof { assert(prefix.len() < a.len()); }
        let max_prefix = max_seq(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
  assert(a.len() > 0);
  let len_int: int = a.len() as int;
  let seq_int: Seq<int> = Seq::new(len_int, |k: int| a@[k] as int);
  let mut min = a[0];
  let mut max = a[0];
  let mut i = 1;
  while i < a.len()
    invariant
      1 <= i <= a.len(),
      i as int == i as int,
      forall |j: int| #![trigger] 0 <= j < i ==> min <= a@[j] as int,
      forall |j: int| #![trigger] 0 <= j < i ==> max >= a@[j] as int,
      min as int == min_seq(seq_int.subrange(0, i as int)),
      max as int == max_seq(seq_int.subrange(0, i as int))
  {
    if a[i] < min {
      min = a[i];
    }
    if a[i] > max {
      max = a[i];
    }
    proof {
      assert(1 <= i <= a.len());
      if i < a.len() {
        assert(min as int == min_seq(seq_int.subrange(0, i as int)));
        assert(max as int == max_seq(seq_int.subrange(0, i as int)));
        if (a[i] as int) < min as int {
          assert(a[i] as int < min as int);
          assert(len_int > i as int);
          assert(a.len() > i);
          assert(seq_int.subrange(0, (i+1) as int) == seq_int.subrange(0, i as int).push(seq_int[i as int]));
          assert(min_seq(seq_int.subrange(0, (i+1) as int)) == a[i] as int);
        } else {
          assert(min_seq(seq_int.subrange(0, (i+1) as int)) == min_seq(seq_int.subrange(0, i as int)));
        }
        if (a[i] as int) > max as int {
          assert(max_seq(seq_int.subrange(0, (i+1) as int)) == a[i] as int);
        } else {
          assert(max_seq(seq_int.subrange(0, (i+1) as int)) == max_seq(seq_int.subrange(0, i as int)));
        }
      }
    }
    i = i + 1;
  }
  proof {
    assert(i == a.len());
    assert(min as int == min_seq(seq_int));
    assert(max as int == max_seq(seq_int));
  }
  (min as i32) + (max as i32)
}
// </vc-code>

fn main() {}

}