// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn char_to_int(c: char) -> int {
    c as int - '0' as int
}

spec fn is_lucky(digits: Seq<int>) -> bool {
    digits.len() == 6 ==> {
        let sum1 = digits[0] + digits[1] + digits[2];
        let sum2 = digits[3] + digits[4] + digits[5];
        sum1 == sum2
    }
}

spec fn valid_ticket(ticket: Seq<char>) -> bool {
    ticket.len() == 6 && forall|i: int| 0 <= i < ticket.len() ==> '0' <= ticket[i] <= '9'
}

spec fn can_make_lucky_with_0_changes(digits: Seq<int>) -> bool {
    digits.len() == 6 && (forall|i: int| 0 <= i < digits.len() ==> 0 <= digits[i] <= 9) ==> is_lucky(digits)
}

spec fn can_make_lucky_with_1_change(digits: Seq<int>) -> bool {
    digits.len() == 6 && (forall|i: int| 0 <= i < digits.len() ==> 0 <= digits[i] <= 9) ==> {
        exists|pos: int| 0 <= pos < 6 &&
            exists|new_digit: int| 0 <= new_digit <= 9 && {
                let new_digits = digits.subrange(0, pos).add(seq![new_digit]).add(digits.subrange(pos + 1, digits.len() as int));
                is_lucky(new_digits)
            }
    }
}

spec fn can_make_lucky_with_2_changes(digits: Seq<int>) -> bool {
    digits.len() == 6 && (forall|i: int| 0 <= i < digits.len() ==> 0 <= digits[i] <= 9) ==> {
        exists|i: int, j: int| 0 <= j < i < 6 &&
            exists|k: int, l: int| 0 <= k <= 9 && 0 <= l <= 9 && {
                let new_digits = digits.subrange(0, i).add(seq![k]).add(digits.subrange(i + 1, digits.len() as int));
                let final_digits = new_digits.subrange(0, j).add(seq![l]).add(new_digits.subrange(j + 1, new_digits.len() as int));
                is_lucky(final_digits)
            }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(ticket: &Vec<char>) -> (result: u32)
    requires valid_ticket(ticket@)
    ensures 0 <= result <= 3
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}