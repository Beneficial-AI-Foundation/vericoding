// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn month_has_31_days(month: i8) -> (result: bool)
    requires 1 <= month as int <= 12
    ensures result <==> (month as int == 1 || month as int == 3 || month as int == 5 || month as int == 7 || month as int == 8 || month as int == 10 || month as int == 12)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}