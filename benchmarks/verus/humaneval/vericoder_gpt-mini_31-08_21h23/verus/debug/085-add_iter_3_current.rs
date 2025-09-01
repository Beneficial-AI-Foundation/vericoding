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
    let mut i: usize = 0;
    let mut sum: u64 = 0;
    // loop over positions 1,3,5,... (0-based indexing: 1,3,...)
    while i + 1 < n
        invariant i <= n && ((sum as int) + add_odd_evens(lst@.skip(i as nat)) == add_odd_evens(lst@))
        decreases n - i
    {
        let prev_sum = sum;
        let x: u32 = lst.get(i + 1);
        // update runtime sum using runtime types only
        if x % 2 == 0 {
            sum = sum + (x as u64);
        } else {
            sum = sum;
        }
        // advance i by 2 and prove the invariant holds (proof uses ghost types)
        let old_i = i;
        i = i + 2;
        proof {
            // s is the remaining sequence before the step
            let s = lst@.skip(old_i as nat);
            // s has length at least 2 because old_i + 1 < n
            assert(s.len() >= 2);
            // by definition of add_odd_evens on sequences of length >= 2
            assert(add_odd_evens(s) == odd_or_zero(s@[1]) + add_odd_evens(s.skip(2)));
            // relate the runtime element x to the corresponding sequence element
            assert(x == lst@[old_i + 1]);
            assert(s@[1] == lst@[old_i + 1]);
            // hence s@[1] == x
            assert(s@[1] == x);
            // relate odd_or_zero(s@[1]) to the runtime value x
            assert(odd_or_zero(s@[1]) == if x % 2 == 0 { x } else { 0 });
            // relate the integer additions: sum == prev_sum + (odd_or_zero(s@[1]) as int)
            assert((sum as int) == (prev_sum as int) + (odd_or_zero(s@[1]) as int));
            // from the invariant before the step: prev_sum + add_odd_evens(s) == add_odd_evens(lst@)
            assert((prev_sum as int) + add_odd_evens(s) == add_odd_evens(lst@));
            // unfold add_odd_evens(s)
            assert((prev_sum as int) + odd_or_zero(s@[1]) + add_odd_evens(s.skip(2)) == add_odd_evens(lst@));
            // convert to int and use the relation for sum
            assert((sum as int) + add_odd_evens(s.skip(2)) == add_odd_evens(lst@));
            // and s.skip(2) == lst@.skip(i) because i == old_i + 2
            assert(s.skip(2) == lst@.skip(i as nat));
            // combine to get the updated invariant
            assert((sum as int) + add_odd_evens(lst@.skip(i as nat)) == add_odd_evens(lst@));
        }
    }
    // After the loop, i >= n-1 so skip(i) has length < 2, hence add_odd_evens(lst@.skip(i)) == 0,
    // so by the invariant sum == add_odd_evens(lst@).
    proof {
        assert(n >= i);
        assert(!(i + 1 < n));
        // i + 1 >= n implies lst@.skip(i).len() < 2
        assert(lst@.skip(i as nat).len() < 2);
        assert(add_odd_evens(lst@.skip(i as nat)) == 0);
        assert((sum as int) + add_odd_evens(lst@.skip(i as nat)) == add_odd_evens(lst@));
        assert((sum as int) == add_odd_evens(lst@));
    }
    sum as u64
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}