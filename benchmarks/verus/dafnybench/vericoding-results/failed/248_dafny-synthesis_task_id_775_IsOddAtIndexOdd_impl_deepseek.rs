use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

proof fn even_implies_not_odd(n: int)
    ensures is_even(n) <==> !is_odd(n)
{
    reveal(is_odd);
    reveal(is_even);
}

proof fn index_range_helper(a: &[int], i: usize)
    requires 0 <= i < a.len()
    ensures 0 <= i < a@.len()
{
    assert(a@.len() == a.len());
}

proof fn exists_counterexample(a: Seq<int>) -> bool
    recommends a.len() > 0
    ensures
        !(forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))) ==>
        exists|i: int| 0 <= i < a.len() && is_odd(i) && !is_odd(a[i])
{
    if !(forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))) {
        assert(exists|i: int| 0 <= i < a.len() && is_odd(i) && !is_odd(a[i]));
    }
    true
}

spec fn is_odd_nat(i: nat) -> bool {
    is_odd(i as int)
}

proof fn odd_nat_helper(i: nat)
    ensures is_odd_nat(i) <==> is_odd(i as int)
{
}

proof fn index_int_to_nat_helper(i: int, a: &[int])
    requires 0 <= i < a.len()
    ensures 0 <= i < a@.len()
{
    assert(a@.len() == a.len());
}
// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &[int]) -> (result: bool)
    ensures result <==> forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))
// </vc-spec>
// <vc-code>
{
    let mut result = true;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            0 < i <= a.len(),
            forall|j: nat| j < i && is_odd_nat(j) ==> is_odd(a[j as usize] as int),
            result == (forall|j: nat| j < i ==> (is_odd_nat(j) ==> is_odd(a[j as usize] as int))),
        decreases a.len() - i
    {
        index_range_helper(a, i);
        proof {
            let j: nat = i as nat;
            if is_odd_nat(j) {
                if !is_odd(a[i] as int) {
                    assert(!is_odd(a[j as usize] as int));
                }
            }
        }
        if is_odd(i as int) {
            if !is_odd(a[i] as int) {
                result = false;
                break;
            }
        }
        if i + 2 <= a.len() {
            i += 2;
        } else {
            break;
        }
    }
    proof {
        exists_counterexample(a@);
        if !result {
            assert(exists|i: int| 0 <= i < a.len() && is_odd(i) && !is_odd(a[i as usize]));
            assert(!(forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i as usize]))));
        } else {
            assert(forall|j: nat| j < a.len() && is_odd_nat(j) ==> is_odd(a[j as usize] as int)) by {
                let mut k: nat = 1;
                while k < a.len() as nat
                    invariant
                        1 <= k <= a.len() as nat,
                        forall|j: nat| j < k && is_odd_nat(j) ==> is_odd(a[j as usize] as int)
                    decreases (a.len() as nat) - k
                {
                    index_int_to_nat_helper(k as int, a);
                    if is_odd_nat(k) {
                        assert(is_odd(a[k as usize] as int));
                    }
                    if k + 2 <= a.len() as nat {
                        k += 2;
                    } else {
                        break;
                    }
                }
                if a.len() > 0 {
                    let j: nat = 0;
                    assert(!is_odd_nat(j));
                }
            };
            assert(forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i as usize])));
        }
    }
    result
}
// </vc-code>

fn main() {
}

}