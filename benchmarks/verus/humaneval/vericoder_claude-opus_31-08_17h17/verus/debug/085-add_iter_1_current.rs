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
proof fn add_odd_evens_unfold(lst: Seq<u32>)
    requires lst.len() >= 2,
    ensures add_odd_evens(lst) == odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2)),
{
    // Unfolds the recursive definition
}

proof fn add_odd_evens_base(lst: Seq<u32>)
    requires lst.len() < 2,
    ensures add_odd_evens(lst) == 0,
{
    // Base case
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
            i <= lst.len() + 1,
            i % 2 == 1,
            sum == add_odd_evens(lst@.take(i as int)),
            sum <= u64::MAX,
    {
        let val = lst[i];
        if val % 2 == 0 {
            sum = sum + val as u64;
        }
        
        assert(lst@.take((i + 2) as int) =~= lst@.take(i as int).push(lst@[i as int]).push(
            if i + 1 < lst.len() { lst@[(i + 1) as int] } else { arbitrary() }
        )) by {
            if i + 1 < lst.len() {
                assert_seqs_equal!(lst@.take((i + 2) as int) == lst@.take(i as int).push(lst@[i as int]).push(lst@[(i + 1) as int]));
            }
        }
        
        if i + 1 < lst.len() {
            proof {
                add_odd_evens_unfold(lst@.take((i + 2) as int));
                assert(lst@.take((i + 2) as int).skip(2) =~= lst@.take(i as int));
                assert(lst@.take((i + 2) as int)[1] == lst@[i as int]);
            }
        } else {
            proof {
                assert(lst@.take((i + 1) as int) =~= lst@);
                add_odd_evens_unfold(lst@);
                assert(lst@.skip(2).take((i - 1) as int) =~= lst@.take(i as int));
            }
        }
        
        i = i + 2;
    }
    
    proof {
        if i == lst.len() + 1 {
            assert(lst@.take((i - 1) as int) =~= lst@);
        } else {
            assert(i == lst.len());
            assert(lst@.take(i as int) =~= lst@);
        }
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}