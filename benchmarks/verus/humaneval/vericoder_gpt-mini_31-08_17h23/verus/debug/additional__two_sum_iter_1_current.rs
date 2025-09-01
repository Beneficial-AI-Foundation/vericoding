use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
/* No helpers required */
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    // pre-conditions-start
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
    // post-conditions-end
// </vc-spec>
// <vc-code>
// <vc-code>
{
    // impl-start
    proof {
        // extract witness pair (p_int, q_int) from the existential precondition
        let (p_int, q_int) = choose(|p: int, q: int|
            0 <= p && p < q && q < nums.len() && nums[p] + nums[q] == target
        );
        // bring them into scope for the rest of the function
        assert(0 <= p_int);
        assert(p_int < q_int);
        assert(q_int < nums.len());
        // convert to usize for looping
        let p_usize: usize = (p_int as int) as usize;
        let q_usize: usize = (q_int as int) as usize;
        // runtime code uses these via outer scope by moving them out of proof block
        // (the following let bindings are shadowing to get holders in non-proof scope)
        let (p_int, q_int) = (p_int, q_int);
        let (p_usize, q_usize) = (p_usize, q_usize);
        // store them in ghost variables (move to outer scope via assert to avoid unused warnings)
        assert(p_int as int == p_int);
        assert(q_int as int == q_int);
    }

    // Recreate p and q in executable scope by using a second choose in a proof to obtain same values.
    // (This is to satisfy Rust scoping: the previous proof-only bindings are not available here.)
    proof {
        let (p_int2, q_int2) = choose(|p: int, q: int|
            0 <= p && p < q && q < nums.len() && nums[p] + nums[q] == target
        );
        assert(0 <= p_int2);
        assert(p_int2 < q_int2);
        assert(q_int2 < nums.len());
    }
    // Now obtain concrete usize witnesses for the rest of the code
    let (p_int, q_int) = choose(|p: int, q: int|
        0 <= p && p < q && q < nums.len() && nums[p] + nums[q] == target
    );
    let p: usize = (p_int as int) as usize;
    let q: usize = (q_int as int) as usize;

    let n = nums.len();

    let mut i: usize = 0;
    while i <= p
        invariant 0 <= i && i <= p + 1
        invariant forall|u: int, v: int|
            0 <= u && u < (i as int) && u < v && v < (n as int)
                ==> nums[u] + nums[v] != target
        decreases (p - i)
    {
        let mut j: usize = i + 1;
        while j < n
            invariant i + 1 <= j && j <= n
            invariant forall|k: int|
                (i as int) + 1 <= k && k < (j as int) ==> nums[i as int] + nums[k] != target
            decreases (n - j)
        {
            if nums[i as int] + nums[j as int] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }

    // After loop, by the outer invariant we have that for all u < i and v>u, no pair sums to target.
    // But since we bounded i by p and p is the first element of a valid pair, reaching here is impossible.
    // Use a proof to derive contradiction and then return a dummy value to satisfy Rust's syntax.
    proof {
        // i must be p + 1 here
        assert(i == p + 1);
        // From the outer invariant, for u = p and v = q we have nums[p] + nums[q] != target,
        // contradicting the chosen witness. Hence this path is unreachable.
        assert(forall|u: int, v: int| 0 <= u && u < (i as int) && u < v && v < (n as int)
            ==> nums[u] + nums[v] != target);
        // contrapositive: instantiate with u = p_int and v = q_int to get contradiction
        assert(0 <= p_int);
        assert(p_int < (i as int));
        assert(p_int < q_int);
        assert(q_int < (n as int));
        // contradiction with nums[p_int] + nums[q_int] == target from the existential
        // Therefore unreachable.
    }

    // unreachable, but return something to satisfy Rust syntax
    (0, 1)
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}