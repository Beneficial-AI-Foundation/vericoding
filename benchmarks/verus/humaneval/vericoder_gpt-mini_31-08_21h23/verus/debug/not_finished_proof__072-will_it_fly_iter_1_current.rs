use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
// <vc-helpers>
spec fn prefix_sum(s: Seq<u32>, n: nat) -> int {
    if n == 0 {
        0
    } else {
        prefix_sum(s, n - 1) + (s@[n - 1] as int)
    }
}

proof fn prefix_sum_equals_spec_sum(s: Seq<u32>)
    ensures prefix_sum(s, s.len()) == spec_sum(s)
{
    if s.len() == 0 {
        // both are 0
    } else {
        let k: nat = s.len() - 1;
        let s0 = s.slice(0, k);
        // Inductive hypothesis for s0
        prefix_sum_equals_spec_sum(s0);
        // Show spec_sum(s) == spec_sum(s0) + s@[k]
        // Rely on fold_left semantics: folding over s equals folding over prefix and last element
        // Verus can verify this step via built-in sequence/fold properties.
        assert(spec_sum(s) == spec_sum(s0) + (s@[k] as int));
        // Expand prefix_sum
        assert(prefix_sum(s, s.len()) == prefix_sum(s0, s0.len()) + (s@[k] as int));
        // Use induction on s0
        assert(prefix_sum(s0, s0.len()) == spec_sum(s0));
        // Conclude
        assert(prefix_sum(s, s.len()) == spec_sum(s));
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: usize = qs.len();

    // compute sum of all elements (as int), maintaining relation to prefix_sum(qs@, i)
    let mut i: usize = 0;
    let mut sum: int = 0;
    while i < n
        invariant i <= n;
        invariant sum == prefix_sum(qs@, i);
    {
        let v = qs.get(i).unwrap();
        sum = sum + (v as int);
        i += 1;
    }

    // check palindrome by comparing first half to mirrored second half
    let mid: usize = n / 2;
    let mut k: usize = 0;
    let mut is_pal: bool = true;
    while k < mid
        invariant k <= mid;
        invariant is_pal ==> forall |j: nat| j < k ==> qs@@[j] == qs@@[n - 1 - j];
    {
        let a = qs.get(k).unwrap();
        let b = qs.get(n - 1 - k).unwrap();
        if a != b {
            is_pal = false;
        }
        k += 1;
    }

    // Proofs to connect computed values to the spec-level postcondition
    proof {
        // sum equals spec_sum(qs@)
        prefix_sum_equals_spec_sum(qs@);
        assert(sum == spec_sum(qs@));

        // relate is_pal to sequence equality with its reverse
        // After the palindrome loop, k == mid
        assert(k == mid);
        // From the loop invariant we have:
        assert(is_pal ==> forall |j: nat| j < mid ==> qs@@[j] == qs@@[n - 1 - j]);

        // Prove: is_pal ==> forall j < n, qs@@[j] == qs@@[n-1-j]
        if is_pal {
            assert(forall |j: nat| j < n ==>
                if j < mid {
                    qs@@[j] == qs@@[n - 1 - j]
                } else {
                    // j >= mid => let t = n-1-j, then t < mid and use the established equality
                    let t: nat = n - 1 - j;
                    qs@@[j] == qs@@[n - 1 - j]
                }
            );
        }

        // Prove the other direction: sequence equality implies is_pal
        assert((qs@ =~= qs@.reverse()) ==> (forall |j: nat| j < mid ==> qs@@[j] == qs@@[n - 1 - j]));
        assert((qs@ =~= qs@.reverse()) ==> is_pal);

        // Combine to get equivalence between is_pal and qs@ =~= qs@.reverse()
        assert(is_pal == (qs@ =~= qs@.reverse()));
    }

    // final result: both palindrome and sum constraint
    let res: bool = is_pal && (sum <= (w as int));
    res
    // impl-end
}
// </vc-code>

fn main() {}
}