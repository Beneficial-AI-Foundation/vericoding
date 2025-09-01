use vstd::prelude::*;

verus! {

// <vc-helpers>
ghost fn closed_interval(a: int, b: int, i: int) -> bool {
    a <= i <= b
}

ghost fn translate_exists<T>(a: int, b: int, f: spec_fn(int) -> bool) -> bool {
    exists|i: int| closed_interval(a, b, i) && f(i)
}

ghost fn exists_split<T>(a: int, b: int, c: int, f: spec_fn(int) -> bool)
    requires a <= b <= c,
    ensures (exists|i: int| closed_interval(a, c, i) && f(i)) == (
        (exists|i: int| closed_interval(a, b, i) && f(i)) ||
        (exists|i: int| closed_interval(b+1, c, i) && f(i))
    )
{
    if exists|i: int| closed_interval(a, c, i) && f(i) {
        let i = choose|i: int| closed_interval(a, c, i) && f(i);
        if closed_interval(a, b, i) {
            assert(exists|i: int| closed_interval(a, b, i) && f(i));
        } else {
            assert(closed_interval(b+1, c, i));
            assert(exists|i: int| closed_interval(b+1, c, i) && f(i));
        }
    }
}

ghost fn exists_one_side<T>(a: int, b: int, c: int, f: spec_fn(int) -> bool)
    requires a <= b <= c,
    ensures (exists|i: int| closed_interval(b+1, c, i) && f(i)) ==> (
        exists|i: int| closed_interval(a, c, i) && f(i)
    )
{
    if exists|i: int| closed_interval(b+1, c, i) && f(i) {
        let i = choose|i: int| closed_interval(b+1, c, i) && f(i);
        assert(closed_interval(a, c, i) && f(i));
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)
    // pre-conditions-start
    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    let mut i = 0;
    let mut found = false;
    
    while i < n
        invariant
            0 <= i <= n,
            found <==> exists|a: int, b: int| 0 <= a < b < i && nums[a] + nums[b] == target,
    {
        let mut j = i + 1;
        while j < n
            invariant
                i < j,
                j <= n,
                found <==> 
                    if i == 0 {
                        false
                    } else {
                        exists|a: int, b: int| 0 <= a < b < i && nums[a] + nums[b] == target
                    } ||
                    exists|b: int| i < b < j && nums[i] + nums[b] == target,
        {
            if nums[i] + nums[j] == target {
                found = true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    found
}
// </vc-code>

fn main() {}
}