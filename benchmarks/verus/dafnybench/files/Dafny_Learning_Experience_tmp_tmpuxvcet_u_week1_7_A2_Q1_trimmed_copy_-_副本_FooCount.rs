// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count(hi: nat, s: Seq<int>) -> int
    recommends 0 <= hi <= s.len()
    decreases hi
{
    if hi == 0 {
        0
    } else if s[hi - 1] % 2 == 0 {
        1 + count((hi - 1) as nat, s)
    } else {
        count((hi - 1) as nat, s)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn foo_count(count_index: usize, a: &Vec<int>, b: &mut Vec<int>) -> (p: usize)
    requires 
        count_index == 0 || (a.len() == old(b).len() && 1 <= count_index <= a.len()),
    ensures 
        p == count(count_index as nat, a@),
    decreases count_index
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}