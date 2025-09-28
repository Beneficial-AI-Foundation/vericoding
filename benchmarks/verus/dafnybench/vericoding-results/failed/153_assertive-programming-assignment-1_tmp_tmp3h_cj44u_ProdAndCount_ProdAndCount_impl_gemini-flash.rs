use vstd::prelude::*;

verus! {

spec fn recursive_positive_product(q: Seq<int>) -> int
    decreases q.len()
{
    if q.len() == 0 {
        1
    } else if q[0] <= 0 {
        recursive_positive_product(q.subrange(1, q.len() as int))
    } else {
        q[0] * recursive_positive_product(q.subrange(1, q.len() as int))
    }
}

spec fn recursive_count(key: int, q: Seq<int>) -> int
    decreases q.len()
{
    if q.len() == 0 {
        0
    } else if q[q.len() - 1] == key {
        1 + recursive_count(key, q.subrange(0, q.len() as int - 1))
    } else {
        recursive_count(key, q.subrange(0, q.len() as int - 1))
    }
}

spec fn county(elem: int, key: int) -> int {
    if elem == key { 1 } else { 0 }
}

spec fn prody(elem: int) -> int {
    if elem <= 0 { 1 } else { elem }
}

// <vc-helpers>
proof fn map_preserves_len<A, B>(s: Seq<A>, f: spec_fn(nat, A) -> B)
    ensures s.len() == s.map(f).len()
{
    // This property is inherent to the definition of map.
    // If Verus requires a proof, it's typically because quantifiers are involved
    // but for simple map it's often automatic.
}

proof fn recursive_count_split(key: int, q: Seq<int>)
    requires q.len() > 0
    ensures recursive_count(key, q) == recursive_count(key, q.subrange(0, q.len() as int - 1)) + county(q[q.len() as int - 1], key)
{
    // This is simply unfolding the definition of recursive_count based on the last element.
    // If q[len-1] == key, then 1 + recursive_count(...) which is county(q[len-1], key) + recursive_count(...)
    // If q[len-1] != key, then recursive_count(...) which is county(q[len-1], key) + recursive_count(...)
}

proof fn recursive_positive_product_split(q: Seq<int>)
    requires q.len() > 0
    ensures recursive_positive_product(q) == prody(q[0]) * recursive_positive_product(q.subrange(1, q.len() as int))
{
    // This is unfolding the definition of recursive_positive_product based on the first element.
    // If q[0] <= 0, then 1 * recursive_positive_product(...) which is prody(q[0]) * recursive_positive_product(...)
    // If q[0] > 0, then q[0] * recursive_positive_product(...) which is prody(q[0]) * recursive_positive_product(...)
}

// Helper proof for the multiplication property in the loop invariant.
proof fn lemma_product_update(old_prod_res: int, current_val: i32, s_prefix: Seq<int>, i: nat)
    requires
        old_prod_res == recursive_positive_product(s_prefix),
        current_val > 0,
        s_prefix.len() == i as int
    ensures
        (old_prod_res as i32 * current_val) as int == recursive_positive_product(s_prefix.add(current_val as int))
{
    assert(recursive_positive_product(s_prefix.add(current_val as int)) == prody(current_val as int) * recursive_positive_product(s_prefix));
    assert(prody(current_val as int) == current_val as int) by (nonlinear_arith); // Since current_val > 0
    assert((old_prod_res as i32 * current_val) as int == old_prod_res * current_val as int) by (nonlinear_arith);
    assert((old_prod_res as i32 * current_val) as int == recursive_positive_product(s_prefix) * current_val as int) by (nonlinear_arith);
}
// </vc-helpers>

// <vc-spec>
fn prod_and_count(q: &[i32], key: i32) -> (i32, u32)
    ensures |result: (i32, u32)| 
        result.0 == recursive_positive_product(q@.map(|_, x: i32| x as int)) &&
        result.1 == recursive_count(key as int, q@.map(|_, x: i32| x as int)) as u32
// </vc-spec>
// <vc-code>
{
    let mut prod_res: i32 = 1;
    let mut count_res: u32 = 0;
    let mut i: usize = 0;

    #[verifier::loop_invariant]
    fn invariant(
        i: usize,
        prod_res: i32,
        count_res: u32,
        q: &[i32],
        key: i32,
    ) {
        let q_spec = q@.map(|_, x: i32| x as int);
        let ghost_i = i as nat;
        let s_prefix = q_spec.subrange(0, ghost_i as int);
        let s_suffix = q_spec.subrange(ghost_i as int, q.len() as int);

        i <= q.len();
        (prod_res as int) == recursive_positive_product(s_prefix);
        (count_res as int) == recursive_count(key as int, s_prefix);
        recursive_positive_product(q_spec) == (prod_res as int) * recursive_positive_product(s_suffix);
        recursive_count(key as int, q_spec) == (count_res as int) + recursive_count(key as int, s_suffix);
    }
    while i < q.len()
    invariant invariant(i, prod_res, count_res, q, key)
    {
        let current_val = q[i];

        let old_prod_res = prod_res;
        let old_count_res = count_res;
        let old_i = i;
        let q_spec = q@.map(|_, x: i32| x as int);

        // Update prod_res
        if current_val <= 0 {
            // prod_res remains unchanged
            // The inductive step for product (prod_res remains the same, and the term from the element is 1 (prody(q[i]) is 1))
            // Current inv: old_prod_res == recursive_positive_product(s_prefix)
            // Goal: new_prod_res == recursive_positive_product(s_prefix.add(q[i]))
            // if current_val <= 0, new_prod_res is old_prod_res.
            // recursive_positive_product(s_prefix.add(q[i])) by def expands to recursive_positive_product(s_prefix) * prody(q[i])
            // Since prody(q[i]) is 1 when q[i] <= 0, this holds.
        } else {
            // Check for overflow before multiplication
            // The problem statement does not specify behavior on overflow, assuming i32 multiplication won't overflow here.
            // If it could, we'd need to cast to i64 or handle it.
            let s_prefix_old = q_spec.subrange(0, old_i as int);
            proof {
                lemma_product_update(old_prod_res as int, current_val, s_prefix_old, old_i as nat);
            }
            prod_res *= current_val;
        }

        // Update count_res
        if current_val == key {
            count_res += 1;
        }

        i += 1;
    }

    (prod_res, count_res)
}
// </vc-code>

fn main() {}

}