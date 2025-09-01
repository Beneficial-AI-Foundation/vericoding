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
proof fn lemma_add_odd_evens_empty(lst: Seq<u32>)
    requires lst.len() < 2,
    ensures add_odd_evens(lst) == 0,
{
}

proof fn lemma_add_odd_evens_step(lst: Seq<u32>)
    requires lst.len() >= 2,
    ensures add_odd_evens(lst) == odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2)),
{
}

proof fn lemma_u64_bounds(sum: u64, next: u32)
    requires sum <= u64::MAX - u32::MAX,
    ensures sum + next as u64 <= u64::MAX,
{
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
            i % 2 == 1,
            1 <= i <= lst.len(),
            sum == add_odd_evens(lst@.take(i as int)),
            sum <= u64::MAX - u32::MAX,
    {
        if lst[i] % 2 == 0 {
            sum = sum + lst[i] as u64;
        }
        
        proof {
            lemma_add_odd_evens_step(lst@.take(i as int + 2));
            assert(lst@.take(i as int + 2).skip(2) == lst@.take(i as int));
        }
        
        i = i + 2;
    }
    
    proof {
        if lst@.len() == lst@.take(i as int).len() {
            assert(lst@ == lst@.take(i as int));
        } else {
            lemma_add_odd_evens_empty(lst@.skip(i as int));
        }
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}