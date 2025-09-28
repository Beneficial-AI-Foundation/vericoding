// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool {
  a >= 1 && a <= 1000 && b >= 2 && b <= 1000
}

spec fn total_burning_hours(a: int, b: int) -> int
  decreases a via a_decreases
{
  if a <= 0 { 0 }
  else if a < b { a }
  else { a + total_burning_hours(a / b, b) }
}

#[verifier::decreases_by]
proof fn a_decreases(a: int, b: int) {
  assume(false);
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): base case of total_burning_hours */
proof fn total_burning_hours_base(a: int, b: int)
    requires
        a >= 1, a < b, b >= 2,
    ensures
        total_burning_hours(a,b) == a,
{
    assert(total_burning_hours(a,b) == if a <= 0 { 0 } else if a < b { a } else { a + total_burning_hours(a / b, b) });
    assert(!(a <= 0));
    assert(a < b);
    assert(total_burning_hours(a,b) == a);
}

/* helper modified by LLM (iteration 5): step case of total_burning_hours */
proof fn total_burning_hours_step(a: int, b: int)
    requires
        a >= b, b >= 2,
    ensures
        total_burning_hours(a,b) == a + total_burning_hours(a / b, b),
{
    assert(total_burning_hours(a,b) == if a <= 0 { 0 } else if a < b { a } else { a + total_burning_hours(a / b, b) });
    assert(!(a <= 0));
    assert(!(a < b));
    assert(total_burning_hours(a,b) == a + total_burning_hours(a / b, b));
}

/* helper modified by LLM (iteration 5): total_burning_hours < 2*a for b>=2 */
proof fn total_burning_hours_lt_2a(a: int, b: int)
    requires
        a >= 1, b >= 2,
    ensures
        total_burning_hours(a,b) < 2 * a,
    decreases a
{
    if a < b {
        assert(total_burning_hours(a,b) == a);
        assert(a < 2 * a);
    } else {
        assert(total_burning_hours(a,b) == a + total_burning_hours(a / b, b));
        total_burning_hours_lt_2a(a / b, b);
        assert(total_burning_hours(a / b, b) < 2 * (a / b));
        assert(total_burning_hours(a,b) < a + 2 * (a / b));
        assert(2 * (a / b) <= a);
        assert(a + 2 * (a / b) <= 2 * a);
        assert(total_burning_hours(a,b) < 2 * a);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
  requires 
    valid_input(a as int, b as int)
  ensures 
    result as int >= a as int,
    result as int == total_burning_hours(a as int, b as int)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): iterative computation syncing runtime and ghost vars to prove correctness */
  let mut aa_r: i64 = a as i64;
  let bb_r: i64 = b as i64;
  let mut acc_r: i64 = 0;

  let ghost mut aa: int = a as int;
  let ghost bb: int = b as int;
  let ghost orig: int = aa;
  let ghost mut acc: int = 0;

  proof {
    total_burning_hours_lt_2a(orig, bb);
    assert(total_burning_hours(orig, bb) < 2 * orig);
    assert(acc + total_burning_hours(aa, bb) == total_burning_hours(orig, bb));
  }

  while aa_r > 0
      invariant
          aa_r >= 0,
          acc_r >= 0,
          acc + total_burning_hours(aa, bb) == total_burning_hours(orig, bb),
          aa_r as int == aa,
          acc_r as int == acc,
          aa_r as int <= orig,
          acc_r as int <= total_burning_hours(orig, bb),
      decreases aa
  {
      if aa_r < bb_r {
          acc_r = acc_r + aa_r;
          proof {
              total_burning_hours_base(aa, bb);
              acc = acc + aa;
              aa = 0;
          }
          aa_r = 0;
      } else {
          acc_r = acc_r + aa_r;
          proof {
              total_burning_hours_step(aa, bb);
              acc = acc + aa;
              aa = aa / bb;
          }
          aa_r = aa_r / bb_r;
      }
  }

  let mut result: i8 = (#[verifier::truncate] acc_r as i8);
  proof {
    assert(acc == acc_r as int);
    assert(acc == total_burning_hours(orig, bb));
  }
  result
}

// </vc-code>


}

fn main() {}