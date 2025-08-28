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

// <vc-helpers>
proof fn count_non_negative(hi: nat, s: Seq<i32>)
    ensures count(hi, s) >= 0
    decreases hi
{
    if hi > 0 {
        count_non_negative((hi - 1) as nat, s);
    }
}

proof fn count_monotonic(hi1: nat, hi2: nat, s: Seq<i32>)
    requires hi1 <= hi2
    ensures count(hi1, s) <= count(hi2, s)
    decreases hi2
{
    if hi1 == hi2 {
    } else if hi2 > 0 {
        count_monotonic(hi1, (hi2 - 1) as nat, s);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn pre_compute(a: &Vec<i32>, b: &mut Vec<i32>) -> (p: usize)
    requires 
        a.len() == old(b).len(),
    ensures 
        (b.len() == 0 || (a.len() == b.len() && 1 <= b.len() <= a.len())) &&
        p == count(b.len() as nat, a@),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn pre_compute(a: &Vec<i32>, b: &mut Vec<i32>) -> (p: usize)
    requires 
        a.len() == old(b).len(),
    ensures 
        b.len() == 0 || (a.len() == b.len() && 1 <= b.len() <= a.len()),
        p == count(b.len() as nat, a@),
{
    let mut count_index = a.len();
    let mut count_result = 0;
    while count_index > 0
        invariant
            0 <= count_index <= a.len(),
            count_result == count((a.len() - count_index) as nat, a@),
    {
        if a[count_index - 1] % 2 == 0 {
            count_result = count_result + 1;
        }
        count_index = count_index - 1;
    }
    b.clear();
    count_result
}
// </vc-code>

fn main() {}

}