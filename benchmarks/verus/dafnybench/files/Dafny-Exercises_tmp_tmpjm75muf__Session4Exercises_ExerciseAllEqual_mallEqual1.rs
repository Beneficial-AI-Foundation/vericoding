use vstd::prelude::*;

verus! {

spec fn all_equal(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}

fn mall_equal1(v: &[i32]) -> (b: bool)
    ensures b == all_equal(v@)
{
    assume(false);
    unreached();
}

}
fn main() {}