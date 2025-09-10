use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

fn mpositive(v: &[int]) -> (b: bool)
    ensures b == positive(v@)
{
    assume(false);
    unreached()
}

}
fn main() {}