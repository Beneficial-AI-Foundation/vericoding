use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn adj_nondec_pair_to_all(l: &Vec<i32>, i: int, j: int)
    requires 0 <= i < j < l@.len()
    requires forall|k: int| 0 <= k < (l@.len() - 1) ==> l@.index(k) <= l@.index(k + 1)
    decreases j - i
{
    if j == i + 1 {
        // direct from adjacent property
        assert(l@.index(i) <= l@.index(j));
    } else {
        // j > i+1
        adj_nondec_pair_to_all(l, i, j - 1);
        // j-1 in range 0 <= j-1 < l.len()-1 since j < l.len()
        assert(l@.index(j - 1) <= l@.index(j));
        // transitivity
        assert(l@.index(i) <= l@.index(j));
    }
}

proof fn adj_nondec_all(l: &Vec<i32>)
    requires forall|k: int| 0 <= k < (l@.len() - 1) ==> l@.index(k) <= l@.index(k + 1)
    ensures forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)
{
    let n = l@.len();
    assert(forall|i: int, j: int| 0 <= i < j < n ==>
        { adj_nondec_pair_to_all(l, i, j); true });
}

proof fn adj_noninc_pair_to_all(l: &Vec<i32>, i: int, j: int)
    requires 0 <= i < j < l@.len()
    requires forall|k: int| 0 <= k < (l@.len() - 1) ==> l@.index(k) >= l@.index(k + 1)
    decreases j - i
{
    if j == i + 1 {
        // direct from adjacent property
        assert(l@.index(i) >= l@.index(j));
    } else {
        // j > i+1
        adj_noninc_pair_to_all(l, i, j - 1);
        // j-1 in range
        assert(l@.index(j - 1) >= l@.index(j));
        // transitivity
        assert(l@.index(i) >= l@.index(j));
    }
}

proof fn adj_noninc_all(l: &Vec<i32>)
    requires forall|k: int| 0 <= k < (l@.len() - 1) ==> l@.index(k) >= l@.index(k + 1)
    ensures forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)
{
    let n = l@.len();
    assert(forall|i: int, j: int| 0 <= i < j < n ==>
        { adj_noninc_pair_to_all(l, i, j); true });
}
// </vc-helpers>

// <vc-spec>
fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n = l.len();
    if n <= 1 {
        return true;
    }
    let m = n - 1;
    let mut i: nat = 0;
    let mut inc: bool = true;
    let mut dec: bool = true;
    while i < m
        invariant 0 <= i <= m
        invariant inc == (forall|k: int| 0 <= k < (i as int) ==> l@.index(k) <= l@.index(k + 1))
        invariant dec == (forall|k: int| 0 <= k < (i as int) ==> l@.index(k) >= l@.index(k + 1))
    {
        let ii: int = i as int;
        let a = l@.index(ii);
        let b = l@.index(ii + 1);
        let prev_inc = inc;
        let prev_dec = dec;
        if a <= b {
            // inc remains prev_inc, which equals previous adjacent conjunction
            inc = prev_inc;
        } else {
            inc = false;
        }
        if a >= b {
            dec = prev_dec;
        } else {
            dec = false;
        }
        // maintain invariants: show new equivalences
        proof {
            // prev_inc == forall k < i ==> l[k] <= l[k+1]
            assert(prev_inc == (forall|k: int| 0 <= k < ii ==> l@.index(k) <= l@.index(k + 1)));
            if a <= b {
                // new adjacent property for k < ii+1 is prev_prop && (a <= b) == prev_inc && true == prev_inc == inc
                assert(inc == (forall|k: int| 0 <= k < (ii + 1) ==> l@.index(k) <= l@.index(k + 1)));
            } else {
                // a > b => new_prop == prev_prop && false == false == inc
                assert(inc == (forall|k: int| 0 <= k < (ii + 1) ==> l@.index(k) <= l@.index(k + 1)));
            }
            // similarly for dec
            assert(prev_dec == (forall|k: int| 0 <= k < ii ==> l@.index(k) >= l@.index(k + 1)));
            if a >= b {
                assert(dec == (forall|k: int| 0 <= k < (ii + 1) ==> l@.index(k) >= l@.index(k + 1)));
            } else {
                assert(dec == (forall|k: int| 0 <= k < (ii + 1) ==> l@.index(k) >= l@.index(k + 1)));
            }
        }
        i += 1;
    }
    let res = inc || dec;
    proof {
        let n_int = n as int;
        // If inc then adjacent nondecreasing holds for all k < n-1, hence all pairs are nondecreasing
        if inc {
            assert(inc == (forall|k: int| 0 <= k < (n_int - 1) ==> l@.index(k) <= l@.index(k + 1)));
            adj_nondec_all(&l);
        }
        // If dec then adjacent nonincreasing holds for all k < n-1, hence all pairs are nonincreasing
        if dec {
            assert(dec == (forall|k: int| 0 <= k < (n_int - 1) ==> l@.index(k) >= l@.index(k + 1)));
            adj_noninc_all(&l);
        }
        // Conversely, if all pairs are nondecreasing then in particular adjacent pairs are, so inc holds
        assert((forall|i: int, j: int| 0 <= i < j < n_int ==> l@.index(i) <= l@.index(j))
            ==> (forall|k: int| 0 <= k < (n_int - 1) ==> l@.index(k) <= l@.index(k + 1)));
        assert((forall|i: int, j: int| 0 <= i < j < n_int ==> l@.index(i) >= l@.index(j))
            ==> (forall|k: int| 0 <= k < (n_int - 1) ==> l@.index(k) >= l@.index(k + 1)));
        // Using the invariants at loop exit, inc/dec reflect the adjacent properties, so the implications hold
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}