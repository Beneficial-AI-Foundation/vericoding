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
fn odd_or_zero_exec(x: u32) -> (ret: u32) {
    if x % 2 == 0 {
        x
    } else {
        0
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
            0 < lst.len(),
            sum == add_odd_evens(lst@.take(i as int).skip(1)),
            i % 2 == 1,
            i <= lst.len(),
    {
        sum = sum + odd_or_zero_exec(lst[i]) as u64;
        proof {
            assert(odd_or_zero_exec(lst[i]) == odd_or_zero(lst@[i as int]));
            assert(i + 2 <= lst.len() || i + 1 == lst.len());
            if (lst.len() < 2) {
                assert(add_odd_evens(lst@.take((i + 2) as int).skip(1)) == 0);
            } else if (i + 2 <= lst.len()) {
                assert(add_odd_evens(lst@.take((i + 2) as int).skip(1)) == odd_or_zero(lst@[i as int]) + add_odd_evens(lst@.take((i + 2) as int).skip(i as int + 2)));
            } else if (i + 1 == lst.len()){
                assert(add_odd_evens(lst@.skip(i as int).take(2)) == odd_or_zero(lst@[i as int])); // odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
            }
            if(i + 2 <= lst.len()) {
                assert(add_odd_evens(lst@.take((i + 2) as int).skip(1)) == odd_or_zero(lst@.index(i as int)) + add_odd_evens(lst@.skip((i + 2) as int)));
            } else {
                assert(add_odd_evens(lst@.take((i + 2) as int).skip(1)) == odd_or_zero(lst@.index(i as int)));
            }
        }
        i = i + 2;
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}