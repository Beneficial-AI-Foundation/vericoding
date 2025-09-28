// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
proof fn step_count_occ_subrange(a: Seq<i32>, key: i32, i: int)
    requires
        0 <= i,
        i < a.len(),
    ensures
        count_occurrences(a.subrange(0, i + 1), key)
            == count_occurrences(a.subrange(0, i), key) + if a.index(i) == key { 1 } else { 0 }
{
}

proof fn lemma_nat_eq1(n: nat)
    ensures
        (n >= 1 && !(n >= 2)) <==> n == 1
{
}
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut seen: bool = false;
    let mut dup: bool = false;
    let mut occ: Ghost<nat> = Ghost(0);

    while i < a.len()
        invariant
            i <= a.len(),
            occ@ == count_occurrences(a@.subrange(0, i as int), key),
            seen == (occ@ >= 1),
            dup == (occ@ >= 2),
        decreases a.len() - i
    {
        let x = a[i];
        if x == key {
            if seen {
                dup = true;
            } else {
                seen = true;
            }
            proof {
                occ = Ghost(occ@ + 1);
            }
        } else {
            proof {
                occ = Ghost(occ@);
            }
        }
        proof {
            step_count_occ_subrange(a@, key, i as int);
        }
        i += 1;
    }

    let result = seen && !dup;
    proof {
        assert(seen == (count_occurrences(a@.subrange(0, a.len() as int), key) >= 1));
        assert(dup == (count_occurrences(a@.subrange(0, a.len() as int), key) >= 2));
        assert(count_occurrences(a@.subrange(0, a.len() as int), key) == count_occurrences(a@, key));
        lemma_nat_eq1(count_occurrences(a@, key));
        assert(result <==> count_occurrences(a@, key) == 1);
    }
    result
}
// </vc-code>

}
fn main() {}