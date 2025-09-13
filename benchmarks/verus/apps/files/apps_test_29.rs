// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn char_to_int(c: char) -> int
{
  c as int - '0' as int
}

spec fn is_lucky(digits: Seq<int>) -> bool
{
  digits.len() == 6 && {
    let sum1 = digits[0] + digits[1] + digits[2];
    let sum2 = digits[3] + digits[4] + digits[5];
    sum1 == sum2
  }
}

spec fn valid_ticket(ticket: &str) -> bool {
  ticket@.len() == 6
}

spec fn can_make_lucky_with_0_changes(digits: Seq<int>) -> bool
{
  is_lucky(digits)
}

spec fn can_make_lucky_with_1_change(digits: Seq<int>) -> bool
{
  digits.len() == 6
}

spec fn can_make_lucky_with_2_changes(digits: Seq<int>) -> bool
{
  digits.len() == 6
}
// </vc-helpers>

// <vc-spec>
fn solve(ticket: &str) -> (result: int)
  requires valid_ticket(ticket)
  ensures 0 <= result <= 3
  ensures
    (let digits = seq![char_to_int(ticket@[0]), char_to_int(ticket@[1]), 
                      char_to_int(ticket@[2]), char_to_int(ticket@[3]),
                      char_to_int(ticket@[4]), char_to_int(ticket@[5])];
     result == 0 <==> can_make_lucky_with_0_changes(digits))
  ensures
    (let digits = seq![char_to_int(ticket@[0]), char_to_int(ticket@[1]), 
                      char_to_int(ticket@[2]), char_to_int(ticket@[3]),
                      char_to_int(ticket@[4]), char_to_int(ticket@[5])];
     result == 1 <==> (!can_make_lucky_with_0_changes(digits) && can_make_lucky_with_1_change(digits)))
  ensures
    (let digits = seq![char_to_int(ticket@[0]), char_to_int(ticket@[1]), 
                      char_to_int(ticket@[2]), char_to_int(ticket@[3]),
                      char_to_int(ticket@[4]), char_to_int(ticket@[5])];
     result == 2 <==> (!can_make_lucky_with_0_changes(digits) && !can_make_lucky_with_1_change(digits) && can_make_lucky_with_2_changes(digits)))
  ensures
    (let digits = seq![char_to_int(ticket@[0]), char_to_int(ticket@[1]), 
                      char_to_int(ticket@[2]), char_to_int(ticket@[3]),
                      char_to_int(ticket@[4]), char_to_int(ticket@[5])];
     result == 3 <==> (!can_make_lucky_with_0_changes(digits) && !can_make_lucky_with_1_change(digits) && !can_make_lucky_with_2_changes(digits)))
// </vc-spec>
// <vc-code>
{
  // impl-start
  assume(false);
  unreached()
  // impl-end
}
// </vc-code>


}

fn main() {}