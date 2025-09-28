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
/* helper modified by LLM (iteration 2): fixed syntax error and removed unnecessary logic */
proof fn lemma_total_burning_hours_unfold(a: int, b: int)
    requires
        a >= 0,
        b >= 2,
    ensures
        b > 0,
        if a < b {
            total_burning_hours(a, b) == a
        } else {
            total_burning_hours(a, b) == a + total_burning_hours(a / b, b)
        },
{
}

/* helper modified by LLM (iteration 2): added decreases clause for recursion */
proof fn lemma_total_hours_bound(a: int, b: int)
    requires
        a >= 1, a <= 127,
        b >= 2, b <= 1000,
    ensures
        total_burning_hours(a, b) < 2 * a,
        total_burning_hours(a, b) <= 247,
    decreases a
{
    if a < b {
        lemma_total_burning_hours_unfold(a, b);
    } else {
        lemma_total_burning_hours_unfold(a, b);
        lemma_total_hours_bound(a / b, b);
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
/* code modified by LLM (iteration 2): fixed compilation errors by using executable integer types and adding loop invariants */
{
    let mut total_hours: i16 = 0;
    let mut candles: i16 = a as i16;
    let b_exec: i16 = b as i16;

    while candles > 0
        invariant
            valid_input(a as int, b as int),
            candles >= 0,
            total_burning_hours(a as int, b as int) == (total_hours as int) + total_burning_hours(candles as int, b as int),
        decreases candles
    {
        ghost {
            lemma_total_burning_hours_unfold(candles as int, b as int);
        }

        total_hours = total_hours + candles;
        candles = candles / b_exec;
    }

    proof {
        assert(total_hours as int == total_burning_hours(a as int, b as int));
    }

    total_hours as i8
}
// </vc-code>


}

fn main() {}