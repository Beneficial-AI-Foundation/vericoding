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

proof fn add_odd_evens_take_skip_lemma(lst: Seq<u32>, i: int)
    requires 
        0 <= i <= lst.len(),
        i % 2 == 1,
    ensures 
        i < lst.len() ==> add_odd_evens(lst.take(i + 1)) == add_odd_evens(lst.take(i - 1)) + odd_or_zero(lst[i - 1]),
        i >= lst.len() ==> add_odd_evens(lst) == add_odd_evens(lst.take(i - 1)),
    decreases lst.len() - i,
{
    if i < lst.len() {
        if i == 1 {
            assert(lst.take(0) =~= Seq::<u32>::empty());
            add_odd_evens_base(lst.take(0));
            assert(add_odd_evens(lst.take(0)) == 0);
            
            if lst.len() >= 2 {
                assert(lst.take(2).len() == 2);
                add_odd_evens_unfold(lst.take(2));
                assert(lst.take(2)[1] == lst[1]);
                assert(lst.take(2).skip(2) =~= Seq::<u32>::empty());
                add_odd_evens_base(lst.take(2).skip(2));
            } else {
                assert(lst.take(2) =~= lst);
                add_odd_evens_base(lst);
            }
        } else {
            assert(i >= 3);
            assert(lst.take(i - 1).len() >= 2);
            add_odd_evens_unfold(lst.take(i - 1));
            
            if i + 1 <= lst.len() {
                assert(lst.take(i + 1).len() >= 2);
                add_odd_evens_unfold(lst.take(i + 1));
                assert(lst.take(i + 1)[1] == lst.take(i - 1)[1]);
                assert(lst.take(i + 1).skip(2) =~= lst.take(i - 1).skip(2).push(lst[i - 1]));
                
                add_odd_evens_take_skip_lemma(lst.take(i - 1).skip(2).push(lst[i - 1]), i - 2);
            } else {
                assert(i == lst.len());
                assert(lst.take(i + 1) =~= lst);
                add_odd_evens_unfold(lst);
                assert(lst[1] == lst.take(i - 1)[1]);
                assert(lst.skip(2) =~= lst.take(i - 1).skip(2).push(lst[i - 1]));
                
                add_odd_evens_take_skip_lemma(lst.skip(2), i - 2);
            }
        }
    } else {
        assert(i >= lst.len());
        assert(lst.take(i - 1) =~= lst);
    }
}

proof fn sum_bound_lemma(lst: Seq<u32>, i: int)
    requires
        0 <= i <= lst.len(),
        i % 2 == 1,
    ensures
        add_odd_evens(lst.take(i)) <= (i / 2) * u32::MAX,
    decreases i,
{
    if i == 1 {
        add_odd_evens_base(lst.take(1));
    } else if i >= 3 {
        sum_bound_lemma(lst, i - 2);
        if i <= lst.len() {
            assert(lst.take(i).len() >= 2);
            add_odd_evens_unfold(lst.take(i));
            assert(add_odd_evens(lst.take(i)) == odd_or_zero(lst.take(i)[1]) + add_odd_evens(lst.take(i).skip(2)));
            assert(lst.take(i).skip(2) =~= lst.take(i - 2));
            assert(odd_or_zero(lst.take(i)[1]) <= u32::MAX);
        }
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
    
    proof {
        add_odd_evens_base(lst@.take(0));
    }
    
    while i < lst.len()
        invariant
            1 <= i <= lst.len() + 1,
            i % 2 == 1,
            sum == add_odd_evens(lst@.take(i - 1)),
            sum <= ((i - 1) / 2) * (u32::MAX as u64),
        decreases lst.len() - i,
    {
        let val = lst[i - 1];
        
        proof {
            sum_bound_lemma(lst@, i as int);
            add_odd_evens_take_skip_lemma(lst@, i as int);
            assert(add_odd_evens(lst@.take(i as int)) == add_odd_evens(lst@.take((i - 1) as int)) + odd_or_zero(lst@[(i - 1) as int]));
        }
        
        if val % 2 == 0 {
            sum = sum + val as u64;
        }
        
        i = i + 2;
    }
    
    proof {
        if i > lst.len() {
            assert(i == lst.len() + 1);
            assert((i - 2) < lst.len());
            add_odd_evens_take_skip_lemma(lst@, (i - 2) as int);
            assert(lst@.take((i - 1) as int) =~= lst@);
        } else {
            assert(i == lst.len());
            assert(i % 2 == 1);
            add_odd_evens_take_skip_lemma(lst@, i as int);
            assert(lst@.take((i - 1) as int) =~= lst@);
        }
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}