use vstd::prelude::*;

verus! {

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
spec fn min_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let min_prefix = min_seq(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let max_prefix = max_seq(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}

// <vc-helpers>
#[verifier(nonlinear_arith)]
proof fn lemma_max_min_len_1(a: Seq<int>)
    requires
        a.len() == 1
    ensures
        min_seq(a) == a[0],
        max_seq(a) == a[0],
{}

#[verifier(nonlinear_arith)]
proof fn lemma_max_min_subrange(a: Seq<int>, len_excluding_last: nat)
    requires
        a.len() > 0,
        len_excluding_last == (a.len() - 1) as nat,
    ensures
        a.subrange(0, len_excluding_last) == a.subrange(0, (a.len() - 1) as int),
{}

#[verifier(nonlinear_arith)]
proof fn lemma_min_seq_le_all(s: Seq<int>, min_val: int)
    requires
        min_val == min_seq(s),
    ensures
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> min_val <= s[i],
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: min_seq(s) is s[0].
        // min_val == s[0] by definition of min_seq for len 1.
        // So, for i=0, min_val <= s[0] is s[0] <= s[0], which is true.
    } else {
        let prefix = s.subrange(0, (s.len() - 1) as int);
        let min_prefix = min_seq(prefix);
        proof {
            min_seq(s); // This is crucial for Verus to expand the definition of min_seq
        }
        lemma_min_seq_le_all(prefix, min_prefix);

        if s.last() <= min_prefix {
            // min_seq(s) is s.last()
            assert(min_val == s.last());
            // We need to show that s.last() <= s[i] for all i.
            // For i = s.len() - 1, it's trivial (s.last() <= s.last()).
            // For i < s.len() - 1:
            // By recursive call, min_prefix <= s[i] for i < prefix.len() (which is s.len() - 1).
            // Since s.last() <= min_prefix, we have s.last() <= min_prefix <= s[i].
            assert forall|i: int| 0 <= i < s.len() implies min_val <= s[i] by {
                if i == s.len() -1 {
                    assert(min_val == s.last());
                } else {
                    assert (i < prefix.len());
                    assert(min_prefix <= s[i]);
                    assert(min_val == s.last());
                    assert(s.last() <= min_prefix); // From the if condition
                    assert(min_val <= s[i]);
                }
            }
        } else {
            // min_seq(s) is min_prefix
            assert(min_val == min_prefix);
            // We need to show that min_prefix <= s[i] for all i.
            // For i < s.len() - 1, it's true by recursive hypothesis: min_prefix <= s[i].
            // For i = s.len() - 1, we know min_prefix < s.last() (from the else condition).
            // So we just need to ensure min_prefix <= s.last().
            assert forall|i: int| 0 <= i < s.len() implies min_val <= s[i] by {
                if i == s.len() - 1 {
                    assert(min_val == min_prefix);
                    assert(min_prefix <= s.last()); // From the else condition of min_seq
                } else {
                    assert(i < prefix.len());
                    assert(min_val == min_prefix);
                    assert(min_prefix <= s[i]); // Recursive hypothesis
                }
            }
        }
    }
}

#[verifier(nonlinear_arith)]
proof fn lemma_max_seq_ge_all(s: Seq<int>, max_val: int)
    requires
        max_val == max_seq(s),
    ensures
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> max_val >= s[i],
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: max_seq(s) is s[0].
        // max_val == s[0] by definition of max_seq for len 1.
        // So, for i=0, max_val >= s[0] is s[0] >= s[0], which is true.
    } else {
        let prefix = s.subrange(0, (s.len() - 1) as int);
        let max_prefix = max_seq(prefix);
        proof {
            max_seq(s); // This is crucial for Verus to expand the definition of max_seq
        }
        lemma_max_seq_ge_all(prefix, max_prefix);

        if s.last() >= max_prefix {
            // max_seq(s) is s.last()
            assert(max_val == s.last());
            // We need to show that s.last() >= s[i] for all i.
            // For i = s.len() - 1, it's trivial (s.last() >= s.last()).
            // For i < s.len() - 1:
            // By recursive call, max_prefix >= s[i] for i < prefix.len() (which is s.len() - 1).
            // Since s.last() >= max_prefix, we have s.last() >= max_prefix >= s[i].
            assert forall|i: int| 0 <= i < s.len() implies max_val >= s[i] by {
                if i == s.len() - 1 {
                    assert(max_val == s.last());
                } else {
                    assert(i < prefix.len());
                    assert(max_prefix >= s[i]);
                    assert(max_val == s.last());
                    assert(s.last() >= max_prefix); // From the if condition
                    assert(max_val >= s[i]);
                }
            }
        } else {
            // max_seq(s) is max_prefix
            assert(max_val == max_prefix);
            // We need to show that max_prefix >= s[i] for all i.
            // For i < s.len() - 1, it's true by recursive hypothesis: max_prefix >= s[i].
            // For i = s.len() - 1, we know max_prefix > s.last() (from the else condition).
            // So we just need to ensure max_prefix >= s.last().
            assert forall|i: int| 0 <= i < s.len() implies max_val >= s[i] by {
                if i == s.len() - 1 {
                    assert(max_val == max_prefix);
                    assert(max_prefix >= s.last()); // From the else condition of max_seq
                } else {
                    assert(i < prefix.len());
                    assert(max_val == max_prefix);
                    assert(max_prefix >= s[i]); // Recursive hypothesis
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let a_seq = a@.map(|_i: int, x: i32| x as int);
    let mut min_val: i32 = a[0];
    let mut max_val: i32 = a[0];
    let mut i: usize = 1;

    let len = a.len();

    // Proven properties for min_seq and max_seq
    if a_seq.len() == 1 {
        proof { lemma_max_min_len_1(a_seq); }
    }

    while i < len
        invariant
            0 < i <= len,
            a.len() > 0,
            a_seq == a@.map(|_i: int, x: i32| x as int),
            // The min_val found so far is the minimum of elements up to i-1
            min_val as int == min_seq(a_seq.subrange(0, i as int)),
            // The max_val found so far is the maximum of elements up to i-1
            max_val as int == max_seq(a_seq.subrange(0, i as int)),
            // For all relevant k, min_val <= a[k] <= max_val
            forall|k: int| 0 <= k < i ==> #[trigger] (min_val as int) <= a_seq[k],
            forall|k: int| 0 <= k < i ==> #[trigger] (max_val as int) >= a_seq[k],
    {
        let current_val = a[i];

        let old_min_val = min_val;
        let old_max_val = max_val;
        let old_i = i;

        if current_val < min_val {
            min_val = current_val;
        }
        if current_val > max_val {
            max_val = current_val;
        }

        proof {
            let next_i = (old_i + 1) as int;
            let current_subseq = a_seq.subrange(0, old_i as int);
            let next_subseq = a_seq.subrange(0, next_i);

            // Establish the length relation for subranges
            assert(current_subseq.len() == old_i as int);
            assert(next_subseq.len() == next_i);
            assert(next_subseq.len() == current_subseq.len() + 1);
            assert(next_subseq.last() == a_seq[old_i as int]);

            assert(min_seq(current_subseq) == old_min_val as int); // From invariant
            assert(max_seq(current_subseq) == old_max_val as int); // From invariant

            // Prove min_seq invariant for next iteration
            // We need to show that `min_val` (the updated one) == `min_seq(next_subseq)`
            if a_seq[old_i as int] <= old_min_val as int {
                // In this case, `min_val` becomes `a_seq[old_i as int]`.
                assert(min_val as int == a_seq[old_i as int]);
                min_seq(next_subseq); 
                assert(min_seq(next_subseq) == a_seq[old_i as int]);
            } else {
                // In this case, `min_val` remains `old_min_val`.
                assert(min_val as int == old_min_val as int);
                min_seq(next_subseq);
                assert(min_seq(next_subseq) == old_min_val as int);
            }
            assert(min_val as int == min_seq(next_subseq));

            // Prove max_seq invariant for next iteration
            // We need to show that `max_val` (the updated one) == `max_seq(next_subseq)`
            if a_seq[old_i as int] >= old_max_val as int {
                // In this case, `max_val` becomes `a_seq[old_i as int]`.
                assert(max_val as int == a_seq[old_i as int]);
                max_seq(next_subseq);
                assert(max_seq(next_subseq) == a_seq[old_i as int]);
            } else {
                // In this case, `max_val` remains `old_max_val`.
                assert(max_val as int == old_max_val as int);
                max_seq(next_subseq);
                assert(max_seq(next_subseq) == old_max_val as int);
            }
            assert(max_val as int == max_seq(next_subseq));

            // Extend the forall property for the next iteration (min_val)
            lemma_min_seq_le_all(next_subseq, min_val as int);

            // Extend the forall property for the next iteration (max_val)
            lemma_max_seq_ge_all(next_subseq, max_val as int);
        }
        i += 1;
    }

    min_val + max_val
}
// </vc-code>

fn main() {}

}