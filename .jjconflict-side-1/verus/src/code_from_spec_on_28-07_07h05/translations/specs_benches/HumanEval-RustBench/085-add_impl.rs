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

fn add(lst: Vec<u32>) -> (sum: u64)
    // pre-conditions-start
    requires
        0 < lst.len() < u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum == add_odd_evens(lst@),
    // post-conditions-end
{
    let mut sum: u64 = 0;
    let mut i: usize = 1;
    
    /* code modified by LLM (iteration 3): fixed loop invariants and overflow prevention */
    while i < lst.len()
        invariant
            i % 2 == 1,
            i >= 1,
            sum == add_odd_evens(lst@.take(i as int)),
            sum <= (lst.len() as u64) * (u32::MAX as u64),
        decreases lst.len() - i,
    {
        /* code modified by LLM (iteration 3): fixed addition with proper overflow check */
        if lst[i] % 2 == 0 {
            assert(sum + (lst[i] as u64) <= sum + (u32::MAX as u64));
            assert(sum + (u32::MAX as u64) <= (lst.len() as u64) * (u32::MAX as u64) + (u32::MAX as u64));
            sum = sum + lst[i] as u64;
        }
        
        /* code modified by LLM (iteration 3): establish invariant before incrementing */
        proof {
            lemma_add_odd_evens_step(lst@, i as int);
        }
        
        i = i + 2;
    }
    
    /* code modified by LLM (iteration 3): use corrected lemma to establish postcondition */
    proof {
        lemma_add_odd_evens_take_complete(lst@, i as int);
    }
    
    sum
}

/* code modified by LLM (iteration 3): helper lemma for single step */
proof fn lemma_add_odd_evens_step(lst: Seq<u32>, i: int)
    requires
        i % 2 == 1,
        i >= 1,
        i + 2 <= lst.len(),
    ensures
        add_odd_evens(lst.take(i + 2)) == add_odd_evens(lst.take(i)) + odd_or_zero(lst[i]),
    decreases lst.len(),
{
    if lst.len() >= 2 {
        let take_i = lst.take(i);
        let take_i2 = lst.take(i + 2);
        
        if i + 2 <= lst.len() {
            assert(take_i2.len() == i + 2);
            assert(take_i.len() == i);
        }
    }
}

/* code modified by LLM (iteration 3): corrected lemma for when loop terminates */
proof fn lemma_add_odd_evens_take_complete(lst: Seq<u32>, i: int)
    requires
        i % 2 == 1,
        i >= lst.len(),
    ensures
        add_odd_evens(lst.take(i)) == add_odd_evens(lst),
    decreases lst.len(),
{
    /* code modified by LLM (iteration 3): when i >= lst.len(), take(i) equals the full sequence */
    if i >= lst.len() {
        assert(lst.take(i) =~= lst) by {
            assert(lst.take(i).len() == lst.len());
            assert(forall |j: int| #![auto] 0 <= j < lst.len() ==> lst.take(i)[j] == lst[j]);
        }
    }
}

} // verus!
fn main() {}