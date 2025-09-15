// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_matches(xs: Seq<u64>, x: u64) -> nat
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        let first_match: nat = if xs[0] == x { 1 } else { 0 };
        first_match + count_matches(xs.skip(1), x)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Changed 'i as nat' to 'i as int' to fix type mismatch in Seq::take method call. */
fn count_matches_exec(xs: &Vec<u64>, x: u64) -> (c: usize)
    ensures
        c@ == count_matches(xs@, x)
{
    let mut count = 0;
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs.len(),
            count@ == count_matches(xs@.take(i as int), x)
        decreases xs.len() - i
    {
        if xs[i] == x {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn majority_element(xs: &Vec<u64>) -> (result: u64)
    requires 
        xs.len() > 0,
        exists|x: u64| count_matches(xs@, x) > xs.len() / 2,
    ensures
        count_matches(xs@, result) > xs.len() / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Implemented majority element finder using a loop to find the element with maximum count via count_matches_exec. */
    let n = xs.len();
    let mut i = 0;
    let mut max_x = 0;
    let mut max_count = 0;
    while i < n
        invariant
            i <= n,
            i > 0 ==> max_count@ == count_matches(xs@, max_x)
        decreases n - i
    {
        let x = xs[i];
        let c = count_matches_exec(xs, x);
        if c > max_count {
            max_count = c;
            max_x = x;
        }
        i = i + 1;
    }
    max_x
}
// </vc-code>

}
fn main() {}