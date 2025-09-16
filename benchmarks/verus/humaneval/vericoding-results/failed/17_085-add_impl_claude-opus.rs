// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to establish final invariant relationship */
proof fn add_odd_evens_bounds(lst: Seq<u32>)
    ensures 
        add_odd_evens(lst) >= 0,
        add_odd_evens(lst) <= lst.len() as int * u32::MAX,
    decreases lst.len(),
{
    if lst.len() < 2 {
    } else {
        add_odd_evens_bounds(lst.skip(2));
    }
}

proof fn add_odd_evens_step(lst: Seq<u32>, i: int)
    requires
        0 <= i,
        i + 2 <= lst.len(),
        i % 2 == 1,
    ensures
        add_odd_evens(lst.take(i + 2)) == add_odd_evens(lst.take(i)) + odd_or_zero(lst[i]),
{
    assert(lst.take(i + 2).skip(2) =~= lst.skip(2).take(i - 1));
    if i == 1 {
        assert(lst.take(1).len() < 2);
        assert(add_odd_evens(lst.take(1)) == 0);
        assert(lst.take(3).len() >= 2);
        assert(add_odd_evens(lst.take(3)) == odd_or_zero(lst[1]) + add_odd_evens(lst.take(3).skip(2)));
        assert(lst.take(3).skip(2) =~= lst.skip(2).take(1));
        assert(lst.skip(2).take(1).len() < 2);
        assert(add_odd_evens(lst.skip(2).take(1)) == 0);
    } else {
        assert(lst.take(i + 2).len() >= 2);
        assert(add_odd_evens(lst.take(i + 2)) == odd_or_zero(lst.take(i + 2)[1]) + add_odd_evens(lst.take(i + 2).skip(2)));
        assert(lst.take(i).len() >= 2);
        assert(add_odd_evens(lst.take(i)) == odd_or_zero(lst.take(i)[1]) + add_odd_evens(lst.take(i).skip(2)));
        assert(lst.take(i + 2)[1] == lst.take(i)[1]);
        assert(lst.take(i + 2).skip(2) =~= lst.skip(2).take(i));
        assert(lst.take(i).skip(2) =~= lst.skip(2).take(i - 2));
    }
}

proof fn add_odd_evens_final(lst: Seq<u32>, i: int)
    requires
        0 < lst.len(),
        i >= lst.len(),
        i % 2 == 1,
        i == lst.len() || i == lst.len() + 1,
    ensures
        add_odd_evens(lst.take(i)) == add_odd_evens(lst),
{
    assert(lst.take(i) =~= lst);
}
// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)

    requires
        0 < lst.len() < u32::MAX,

    ensures
        sum == add_odd_evens(lst@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant and added proper bounds checking */
    let mut sum: u64 = 0;
    let mut i: usize = 1;
    
    proof {
        add_odd_evens_bounds(lst@);
    }
    
    while i < lst.len()
        invariant
            1 <= i,
            i % 2 == 1,
            i == 1 || i == lst.len() + 1 || i <= lst.len(),
            sum == add_odd_evens(lst@.take(i as int)),
            sum <= lst.len() as int * u32::MAX,
        decreases lst.len() - i,
    {
        proof {
            add_odd_evens_step(lst@, i as int);
            add_odd_evens_bounds(lst@.take((i + 2) as int));
        }
        
        if lst[i] % 2 == 0 {
            let old_sum = sum;
            sum = sum + lst[i] as u64;
            proof {
                assert(odd_or_zero(lst@[i as int]) == lst[i]);
                assert(sum == old_sum + lst[i] as u64);
            }
        } else {
            proof {
                assert(odd_or_zero(lst@[i as int]) == 0);
            }
        }
        
        i = i + 2;
        
        proof {
            if i > lst.len() {
                assert(lst@.take(i as int) =~= lst@);
            }
        }
    }
    
    proof {
        add_odd_evens_final(lst@, i as int);
    }
    
    sum
}
// </vc-code>

}
fn main() {}