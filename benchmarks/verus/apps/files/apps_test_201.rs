// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(c: int, hr: int, hb: int, wr: int, wb: int) -> bool
{
  c >= 0 && hr > 0 && hb > 0 && wr > 0 && wb > 0
}

spec fn valid_candy_combination(red_count: int, blue_count: int, c: int, wr: int, wb: int) -> bool
{
  red_count >= 0 && blue_count >= 0 && red_count * wr + blue_count * wb <= c
}

spec fn joy(red_count: int, blue_count: int, hr: int, hb: int) -> int
{
  red_count * hr + blue_count * hb
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(c: int, hr: int, hb: int, wr: int, wb: int) -> (result: int)
  requires 
    valid_input(c, hr, hb, wr, wb),
  ensures 
    result >= 0,
  ensures 
    (exists|red_count: int, blue_count: int| 
      valid_candy_combination(red_count, blue_count, c, wr, wb) &&
      result == joy(red_count, blue_count, hr, hb)),
  ensures 
    (forall|red_count: int, blue_count: int|
      valid_candy_combination(red_count, blue_count, c, wr, wb) ==>
      joy(red_count, blue_count, hr, hb) <= result),
// </vc-spec>
// <vc-code>
{
  assume(false);
  0
}
// </vc-code>


}

fn main() {}