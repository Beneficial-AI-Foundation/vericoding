// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count(hi: nat, s: Seq<i32>) -> int
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

fn compute_count(count_index: usize, a: &Vec<i32>, b: &mut Vec<i32>) -> (p: usize)
    requires 
        count_index == 0 || (a.len() == old(b).len() && 1 <= count_index <= a.len()),
    ensures 
        p == count(count_index as nat, a@),
{
  assume(false);
  0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn pre_compute(a: &Vec<i32>, b: &mut Vec<i32>) -> (p: usize)
    requires 
        a.len() == old(b).len(),
    ensures 
        (b.len() == 0 || (a.len() == b.len() && 1 <= b.len() <= a.len())) &&
        p == count(b.len() as nat, a@),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}