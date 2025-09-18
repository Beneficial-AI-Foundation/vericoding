// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prefix_count for Seq prefix counts */
spec fn prefix_count(a: Seq<i32>, i: nat, key: i32) -> nat
    decreases
        i
{
    if i == 0 {
        0
    } else {
        let prev = prefix_count(a, i - 1, key);
        if a@[i - 1] == key {
            prev + 1
        } else {
            prev
        }
    }
}

/* helper modified by LLM (iteration 5): lemma relating prefix_count to count_occurrences */
lemma fn prefix_count_equiv_count(a: Seq<i32>, key: i32)
    ensures
        prefix_count(a, a.len(), key) == count_occurrences(a, key),
{
    proof {
        let n = a.len();
        if n == 0 {
            assert(prefix_count(a, 0, key) == 0);
            assert(count_occurrences(a, key) == 0);
        } else {
            let n1 = n - 1;
            let ap = a[..n1];
            // apply induction on the prefix
            prefix_count_equiv_count(ap, key);
            // unfold the recursive definitions for the last element
            assert(prefix_count(a, n, key) == prefix_count(a, n1, key) + (if a@[n1] == key { 1 } else { 0 }));
            assert(count_occurrences(a, key) == count_occurrences(ap, key) + (if a@[n1] == key { 1 } else { 0 }));
            assert(prefix_count(a, n1, key) == count_occurrences(ap, key));
            assert(prefix_count(a, n, key) == count_occurrences(a, key));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over sequence a@ counting occurrences using prefix_count invariant */
    let n: nat = (a@).len();
    let mut i: nat = 0;
    let mut cnt: nat = 0;
    while i < n
        invariant
            i <= n,
            cnt == prefix_count(a@, i, key),
        decreases n - i
    {
        if (a@)@[i] == key {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    proof {
        assert(cnt == prefix_count(a@, n, key));
        prefix_count_equiv_count(a@, key);
        assert(prefix_count(a@, n, key) == count_occurrences(a@, key));
        assert((cnt == 1) <==> (count_occurrences(a@, key) == 1));
    }
    let result = cnt == 1;
    result
}

// </vc-code>

}
fn main() {}