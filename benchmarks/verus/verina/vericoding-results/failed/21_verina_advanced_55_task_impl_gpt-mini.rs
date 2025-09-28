// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): count_prefix for seq prefixes */
spec fn count_prefix(xs: Seq<i32>, target: i32, upto: int) -> nat
    decreases upto
{
    if upto <= 0 {
        0
    } else {
        let prev = count_prefix(xs, target, upto - 1);
        if xs[upto - 1] == target { prev + 1 } else { prev }
    }
}

/* helper modified by LLM (iteration 5): simple spec max for nat */
spec fn max_nat(a: nat, b: nat) -> nat {
    if a < b { b } else { a }
}

// </vc-helpers>

// <vc-spec>
fn most_frequent(xs: Vec<i32>) -> (result: i32)
    requires xs.len() > 0,
    ensures
        xs@.contains(result),
        forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= count_occurrences(xs@, result),
        exists|first_idx: int| 
            0 <= first_idx < xs.len() && 
            xs[first_idx] == result && 
            count_occurrences(xs@, result) == count_occurrences(xs@, xs[first_idx]) &&
            forall|i: int| 0 <= i < first_idx ==> count_occurrences(xs@, xs[i]) < count_occurrences(xs@, result),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): scan to find earliest most frequent element using nested scans and proofs */
    let n = xs.len();
    let mut best_idx: usize = 0;
    let mut best_count: usize = 0;

    // compute count for xs[0]
    let v0 = xs[0];
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == xs.len(),
            best_count <= n,
            (best_count as nat) == count_prefix(xs@, v0, k as int),
        decreases n - k
    {
        if xs[k] == v0 {
            best_count += 1;
        }
        k += 1;
    }
    proof {
        assert((best_count as nat) == count_prefix(xs@, v0, n as int));
        assert(count_occurrences(xs@, v0) == (best_count as nat));
    }

    let mut i: usize = 1;
    while i < n
        invariant
            i <= n,
            n == xs.len(),
            best_idx < n,
            best_count <= n,
            forall|j: int| 0 <= j < (i as int) ==> count_occurrences(xs@, xs@[(j as int)]) <= count_occurrences(xs@, xs@[(best_idx as int)]),
        decreases n - i
    {
        let v = xs[i];
        let mut c: usize = 0;
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                n == xs.len(),
                c <= n,
                (c as nat) == count_prefix(xs@, v, j as int),
            decreases n - j
        {
            if xs[j] == v { c += 1; }
            j += 1;
        }
        proof {
            assert((c as nat) == count_prefix(xs@, v, n as int));
            assert(count_occurrences(xs@, v) == (c as nat));
        }
        if c > best_count {
            best_count = c;
            best_idx = i;
        }
        i += 1;
        proof {
            assert(forall|jj: int| 0 <= jj < (i as int) ==> count_occurrences(xs@, xs@[(jj as int)]) <= count_occurrences(xs@, xs@[(best_idx as int)]));
        }
    }

    proof {
        assert(best_idx < n);
        assert((best_count as nat) == count_occurrences(xs@, xs@[(best_idx as int)]));
        assert(forall|j: int| 0 <= j < (best_idx as int) ==> count_occurrences(xs@, xs@[(j as int)]) < count_occurrences(xs@, xs@[(best_idx as int)]));
    }

    xs[best_idx]
}

// </vc-code>

}
fn main() {}