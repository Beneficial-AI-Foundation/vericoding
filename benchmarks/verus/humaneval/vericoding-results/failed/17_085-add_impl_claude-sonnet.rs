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
spec fn add_odd_evens_iter(lst: Seq<u32>, i: int) -> int
    decreases lst.len() - i,
{
    if i + 1 >= lst.len() {
        0
    } else {
        odd_or_zero(lst[i + 1]) + add_odd_evens_iter(lst, i + 2)
    }
}

proof fn add_odd_evens_equiv(lst: Seq<u32>)
    ensures add_odd_evens(lst) == add_odd_evens_iter(lst, 0),
    decreases lst.len(),
{
    if lst.len() < 2 {
        assert(add_odd_evens(lst) == 0);
        assert(add_odd_evens_iter(lst, 0) == 0);
    } else {
        let tail = lst.skip(2);
        add_odd_evens_equiv(tail);
        assert(add_odd_evens(tail) == add_odd_evens_iter(tail, 0));
        assert(add_odd_evens_iter(tail, 0) == add_odd_evens_iter(lst, 2));
    }
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
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and invariant issues */
    let mut sum: u64 = 0;
    let mut i: usize = 0;
    
    proof {
        add_odd_evens_equiv(lst@);
    }
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            i % 2 == 0,
            sum == add_odd_evens_iter(lst@, i as int) as u64,
        decreases lst.len() - i,
    {
        if i + 1 < lst.len() && lst[i + 1] % 2 == 0 {
            sum = sum + lst[i + 1] as u64;
        }
        i = i + 2;
    }
    
    sum
}
// </vc-code>

}
fn main() {}