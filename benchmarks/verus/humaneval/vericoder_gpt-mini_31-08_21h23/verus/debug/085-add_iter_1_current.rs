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
// No helpers required for this proof.
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
    // impl-start
    let n = lst.len();
    let mut i: nat = 0;
    let mut sum: int = 0;
    // loop over positions 1,3,5,... (0-based indexing: 1,3,...)
    while i + 1 < n
        invariant i <= n
        invariant (sum + add_odd_evens(lst@.skip(i)) == add_odd_evens(lst@))
        decreases n - i
    {
        let x = lst.get(i + 1);
        if x % 2 == 0 {
            sum = sum + (x as int);
        } else {
            sum = sum + 0;
        }
        // update i by 2 and prove the invariant holds
        let old_i = i;
        i = i + 2;
        proof {
            // let s be the remaining sequence before the step
            let s = lst@.skip(old_i);
            // s has length at least 2 because old_i + 1 < n
            assert(s.len() >= 2);
            // by definition of add_odd_evens on sequences of length >= 2
            assert(add_odd_evens(s) == odd_or_zero(s@[1]) + add_odd_evens(s.skip(2)));
            // relate the runtime element x to the corresponding sequence element
            assert(s@[1] == lst@[old_i + 1]);
            // now relate the integer additions:
            if x % 2 == 0 {
                // x is even, so odd_or_zero(s@[1]) equals lst@[old_i + 1]
                assert(odd_or_zero(s@[1]) == (x as u32)); // both are same u32
                assert((sum - (x as int)) + odd_or_zero(s@[1]) == sum);
            } else {
                // x is odd, odd_or_zero(s@[1]) == 0
                assert(odd_or_zero(s@[1]) == 0);
                assert(sum == sum);
            }
            // combine equalities to get the updated invariant
            assert((sum) + add_odd_evens(lst@.skip(i)) == ( (sum - (if x % 2 == 0 { x as int } else { 0 })) + odd_or_zero(s@[1]) + add_odd_evens(s.skip(2)) ));
            // from earlier equalities
            assert((sum) + add_odd_evens(lst@.skip(i)) == sum + add_odd_evens(s.skip(2)));
            // and from the unfolding of add_odd_evens(s) we have
            assert(sum + add_odd_evens(s.skip(2)) == add_odd_evens(lst@));
            // thus the invariant holds after the step
        }
    }
    // After the loop, i >= n-1 so skip(i) has length < 2, hence add_odd_evens(lst@.skip(i)) == 0,
    // so by the invariant sum == add_odd_evens(lst@).
    proof {
        assert(n >= i);
        assert(lst@.skip(i).len() < 2);
        assert(add_odd_evens(lst@.skip(i)) == 0);
        assert(sum + add_odd_evens(lst@.skip(i)) == add_odd_evens(lst@));
        assert(sum == add_odd_evens(lst@));
    }
    sum as u64
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}