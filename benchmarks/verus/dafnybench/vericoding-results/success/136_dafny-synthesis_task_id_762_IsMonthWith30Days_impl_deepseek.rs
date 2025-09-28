use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_month_30(month: int)
    requires 1 <= month <= 12
    ensures month == 4 || month == 6 || month == 9 || month == 11 <==> seq![4int, 6int, 9int, 11int].contains(month)
{
    let s = seq![4int, 6int, 9int, 11int];
    assert(s.contains(4));
    assert(s.contains(6));
    assert(s.contains(9));
    assert(s.contains(11));
    assert(!s.contains(1));
    assert(!s.contains(2));
    assert(!s.contains(3));
    assert(!s.contains(5));
    assert(!s.contains(7));
    assert(!s.contains(8));
    assert(!s.contains(10));
    assert(!s.contains(12));
}
// </vc-helpers>

// <vc-spec>
fn is_month_with_30_days(month: i32) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> (month == 4 || month == 6 || month == 9 || month == 11)
// </vc-spec>
// <vc-code>
{
    proof { lemma_month_30(month as int); }
    month == 4 || month == 6 || month == 9 || month == 11
}
// </vc-code>

fn main() {
}

}