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
    requires lst.len() < 2
    ensures add_odd_evens(lst) == 0
{
}

proof fn lemma_add_odd_evens_step(lst: Seq<u32>)
    requires lst.len() >= 2
    ensures add_odd_evens(lst) == odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
{
}

proof fn lemma_u32_to_u64_bounds(x: u32)
    ensures x as u64 <= u32::MAX as u64
{
}

proof fn lemma_sum_bounds(sum: u64, val: u32)
    requires sum <= (u32::MAX as u64) * (u32::MAX as u64)
    ensures sum + (val as u64) <= (u32::MAX as u64) * (u32::MAX as u64) + (u32::MAX as u64)
{
}

proof fn lemma_add_odd_evens_take_step(lst: Seq<u32>, i: int)
    requires i % 2 == 1
    requires 1 <= i < lst.len()
    ensures add_odd_evens(lst.take(i + 2)) == add_odd_evens(lst.take(i)) + odd_or_zero(lst[i])
{
    let lst_i = lst.take(i);
    let lst_i2 = lst.take(i + 2);
    
    if i == 1 {
        assert(lst_i.len() == 1);
        assert(lst_i2.len() == 3);
        assert(add_odd_evens(lst_i) == 0);
        assert(add_odd_evens(lst_i2) == odd_or_zero(lst_i2[1]) + add_odd_evens(lst_i2.skip(2)));
        assert(lst_i2[1] == lst[1]);
        assert(lst_i2.skip(2).len() == 1);
        assert(add_odd_evens(lst_i2.skip(2)) == 0);
    } else {
        assert(lst_i.len() >= 2);
        assert(lst_i2.len() >= 2);
        lemma_add_odd_evens_step(lst_i);
        lemma_add_odd_evens_step(lst_i2);
        lemma_add_odd_evens_take_step(lst, i - 2);
    }
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
            0 < lst.len() < u32::MAX,
            1 <= i <= lst.len(),
            i % 2 == 1,
            sum == add_odd_evens(lst@.take(i as int)),
            sum <= (u32::MAX as u64) * (lst.len() as u64)
        decreases lst.len() - i
    {
        let val = lst[i];
        if val % 2 == 0 {
            proof {
                lemma_u32_to_u64_bounds(val);
                lemma_sum_bounds(sum, val);
            }
            sum = sum + (val as u64);
        }
        
        proof {
            if i + 2 <= lst.len() {
                lemma_add_odd_evens_take_step(lst@, i as int);
            }
        }
        
        i = i + 2;
    }
    
    proof {
        assert(lst@.take(lst.len() as int) == lst@);
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}