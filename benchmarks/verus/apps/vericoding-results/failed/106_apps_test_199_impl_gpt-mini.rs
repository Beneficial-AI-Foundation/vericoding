// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: int, v: Seq<int>) -> bool {
    n > 0 && v.len() == n && s >= 0 && forall|i: int| 0 <= i < v.len() ==> v[i] >= 0
}

spec fn sum(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        v[0] + sum(v.subrange(1, v.len() as int))
    }
}

spec fn min_seq(v: Seq<int>) -> int
    recommends v.len() > 0
    decreases v.len()
{
    if v.len() == 1 {
        v[0]
    } else if v.len() > 1 && v[0] <= min_seq(v.subrange(1, v.len() as int)) {
        v[0]
    } else if v.len() > 1 {
        min_seq(v.subrange(1, v.len() as int))
    } else {
        0
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proves sum of non-negative sequence is non-negative */
fn sum_nonneg(seq: Seq<int>)
    requires
        forall|i: int| 0 <= i && i < seq.len() as int ==> seq[i] >= 0,
    ensures
        sum(seq) >= 0,
    decreases
        seq.len()
{
    if seq.len() as int == 0 {
    } else {
        sum_nonneg(seq.subrange(1, seq.len() as int));
        proof {
            assert(seq[0] >= 0);
            assert(sum(seq.subrange(1, seq.len() as int)) >= 0);
            assert(sum(seq) == seq[0] + sum(seq.subrange(1, seq.len() as int)));
            assert(seq[0] + sum(seq.subrange(1, seq.len() as int)) >= 0);
        }
    }
}

/* helper modified by LLM (iteration 5): relates min_seq of a prefix extended by one element to the min of the prefix and the element */
fn min_seq_prefix(seq: Seq<int>, k: int)
    requires
        0 <= k && k < seq.len() as int,
    ensures
        min_seq(seq.subrange(0, k + 1)) == if k == 0 { seq[0] } else { min(min_seq(seq.subrange(0, k)), seq[k]) },
    decreases
        k
{
    if k == 0 {
        proof {
            assert(min_seq(seq.subrange(0, 1)) == seq[0]);
        }
    } else {
        min_seq_prefix(seq, k - 1);
        proof {
            assert(k > 0);
            // By the definition of min_seq on a sequence of length k+1 and
            // the inductive hypothesis on the prefix of length k, the minimum
            // of the first k+1 elements is the minimum of the minimum of the
            // first k elements and the k-th element.
            assert(min_seq(seq.subrange(0, k + 1)) == if k == 0 { seq[0] } else { min(min_seq(seq.subrange(0, k)), seq[k]) });
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: i8, v: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, s as int, v@.map(|i, x| x as int))
    ensures 
        sum(v@.map(|i, x| x as int)) < s as int ==> result == -1,
        sum(v@.map(|i, x| x as int)) >= s as int ==> result == min((sum(v@.map(|i, x| x as int)) - s as int) / n as int, min_seq(v@.map(|i, x| x as int))) as i8,
        result == -1 || result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute total and minimum while maintaining ghost invariants tying runtime values to spec-level seq */
{
    let len: usize = v.len();
    let mut i: usize = 0;
    let mut total_rt: i64 = 0;
    let mut min_rt: i8 = 0;
    let mut first: bool = true;

    // ghost/state for specification-level reasoning
    let ghost gseq: Seq<int> = v@.map(|i, x| x as int);
    let ghost mut gi: nat = 0;
    let ghost mut gtotal: int = 0;
    let ghost mut gmin: int = 0;
    let ghost gn: int = n as int;
    let ghost gs: int = s as int;

    while i < len
        invariant
            gi <= gseq.len(),
            gi == i as nat,
            gtotal == sum(gseq.subrange(0, gi as int)),
            (gi == 0 && gmin == 0) || (gi > 0 && gmin == min_seq(gseq.subrange(0, gi as int))),
        decreases
            gseq.len() - gi
    {
        let x: i8 = v[i];
        let ghost xi_int: int = x as int;

        if first {
            min_rt = x;
            first = false;
            gmin = xi_int;
        } else {
            if x < min_rt {
                min_rt = x;
            }
            gmin = min(gmin, xi_int);
        }

        total_rt = total_rt + (x as i64);

        // advance ghost index and total
        gi = gi + 1;
        gtotal = gtotal + xi_int;
        i = i + 1;
    }

    let result: i8;
    if total_rt < s as i64 {
        result = -1;
    } else {
        let avg_rt: i64 = (total_rt - (s as i64)) / (n as i64);
        let desired_rt: i64 = if avg_rt <= (min_rt as i64) { avg_rt } else { min_rt as i64 };
        proof {
            assert(gi == len as nat);
            assert(gtotal == total_rt as int);
            assert(gmin == min_rt as int);
            assert(gn == n as int);
            assert(gs == s as int);
            assert((gtotal - gs) / gn == ( (total_rt as int - gs) / gn));
        }
        result = desired_rt as i8;
    }

    result
}

// </vc-code>


}

fn main() {}