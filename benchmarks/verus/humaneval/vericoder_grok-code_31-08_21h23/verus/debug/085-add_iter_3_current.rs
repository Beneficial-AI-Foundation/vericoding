use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}
// pure-end
// pure-end

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// pure-end

// <vc-helpers>
spec fn sum_odd_positions(seq: Seq<u32>, start: usize) -> int
    requires start <= seq.len()
    decreases (seq.len() - start) as nat
{
    if start >= seq.len() { 0 } else { odd_or_zero(seq[start]) as int + sum_odd_positions(seq, start + 2) }
}
// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)
    // pre-conditions-start
    requires
        0 < lst.len() < u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum == add_odd_evens(lst@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut sum: u64 = 0;
    let mut i: usize = 1;
    while i < lst.len()
        invariant
            0 < lst.len() < u32::MAX as usize,
            1 <= i <= lst.len(),
            sum as int == add_odd_evens(lst@) - sum_odd_positions(lst@, i),
    {
        let add = if lst[i] % 2 == 0 { lst[i] as u64 } else { 0 };
        sum += add;
        i += 2;
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}