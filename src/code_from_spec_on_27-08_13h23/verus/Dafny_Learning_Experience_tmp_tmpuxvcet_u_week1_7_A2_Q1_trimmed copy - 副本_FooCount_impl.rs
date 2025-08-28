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

// <vc-helpers>
proof fn lemma_count_decreases(hi: nat, s: Seq<int>)
    requires 0 <= hi <= s.len()
    ensures count(hi, s) >= 0
    decreases hi
{
    if hi > 0 {
        lemma_count_decreases((hi - 1) as nat, s);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn foo_count(count_index: usize, a: &Vec<int>, b: &mut Vec<int>) -> (p: usize)
    requires 
        count_index == 0 || (a.len() == old(b).len() && 1 <= count_index <= a.len()),
    ensures 
        p == count(count_index as nat, a@),
    decreases count_index
// </vc-spec>
// </vc-spec>

// <vc-code>
fn foo_count(count_index: usize, a: &Vec<int>, b: &mut Vec<int>) -> (p: usize)
    requires 
        count_index == 0 || (a.len() == old(b).len() && 1 <= count_index <= a.len()),
    ensures 
        p == count(count_index as nat, a@),
    decreases count_index
{
    if count_index == 0 {
        return 0;
    }
    let mut result = 0;
    if a[count_index - 1] % 2 == 0 {
        result = 1;
    }
    let next_result = foo_count(count_index - 1, a, b);
    result + next_result
}
// </vc-code>

fn main() {}

}