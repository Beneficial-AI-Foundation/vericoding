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

proof fn lemma_decreases(i: usize, len: usize)
    requires i < len, i % 2 == 1,
    ensures (len - (i + 2)) < (len - i),
{
}

proof fn lemma_take_skip_relation(lst: Seq<u32>, i: int)
    requires i >= 0, i + 2 <= lst.len(),
    ensures lst.take(i + 2).skip(2) == lst.take(i),
{
}

proof fn lemma_add_odd_evens_extend(lst: Seq<u32>, i: int)
    requires i >= 1, i % 2 == 1, i + 2 <= lst.len(),
    ensures add_odd_evens(lst.take(i + 2)) == add_odd_evens(lst.take(i)) + odd_or_zero(lst[i]),
{
    lemma_add_odd_evens_step(lst.take(i + 2));
    lemma_take_skip_relation(lst, i);
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
        decreases lst.len() - i,
    {
        proof {
            lemma_add_odd_evens_extend(lst@, i as int);
        }
        
        if lst[i] % 2 == 0 {
            proof {
                lemma_u64_bounds(sum, lst@[i as int]);
            }
            sum = sum + lst[i] as u64;
        }
        
        i = i + 2;
    }
    
    proof {
        if i as int >= lst@.len() {
            assert(lst@.take(i as int) == lst@);
        }
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}