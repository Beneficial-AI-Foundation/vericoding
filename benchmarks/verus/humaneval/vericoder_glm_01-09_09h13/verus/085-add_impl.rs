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
proof fn lemma_skip_twice<T>(s: Seq<T>) {
    assert(s.skip(2).skip(2) == s.skip(4));
}

proof fn lemma_add_odd_evens_split(lst: Seq<u32>) {
    if lst.len() < 2 {
        assert(add_odd_evens(lst) == 0);
    } else {
        assert(add_odd_evens(lst) == odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2)));
    }
}

proof fn lemma_odd_or_zero_ge_zero(x: u32) {
    assert(odd_or_zero(x) >= 0);
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
    
    proof {
        lemma_odd_or_zero_ge_zero(lst@[1]);
    }
    
    while i < lst.len() {
        invariant(
            0 <= i <= lst.len(),
            sum <= add_odd_evens(lst@.subrange(0, i + 1)),
        );
        
        if i % 2 == 1 {
            proof {
                lemma_add_odd_evens_split(lst@.subrange(0, i));
            }
            sum += odd_or_zero(lst[i]) as u64;
        }
        i += 1;
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}