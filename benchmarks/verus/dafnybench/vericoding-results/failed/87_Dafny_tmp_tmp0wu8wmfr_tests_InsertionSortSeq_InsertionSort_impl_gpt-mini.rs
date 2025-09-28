use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
spec fn seq_unit(x: int) -> Seq<int> {
    Seq::from_slice::<int>(&[x])
}

spec fn seq_cons(x: int, s: Seq<int>) -> Seq<int> {
    seq![x] + s
}

#[verifier(nonlinear)]
proof fn insert_sorted_spec(s: Seq<int>, x: int) -> Seq<int>
    ensures
        is_sorted(ret),
        ret.len() == s.len() + 1,
        ret.to_multiset() == s.to_multiset() + seq_unit(x).to_multiset()
{
    if s.len() == 0 {
        let r = seq![x];
        proof {
        }
        r
    } else {
        if x <= s@[0] {
            let r = seq![x] + s;
            proof {
            }
            r
        } else {
            let tail = insert_sorted_spec(s.slice(1, s.len()), x);
            let r = seq![s@[0]] + tail;
            proof {
            }
            r
        }
    }
}

#[verifier(nonlinear)]
proof fn insertion_sort_spec(s: Seq<int>) -> Seq<int>
    ensures
        is_sorted(ret),
        ret.len() == s.len(),
        ret.to_multiset() == s.to_multiset()
{
    if s.len() == 0 {
        let r = Seq::empty();
        proof {
        }
        r
    } else {
        let tail_sorted = insertion_sort_spec(s.slice(1, s.len()));
        let r = insert_sorted_spec(tail_sorted, s@[0]);
        proof {
        }
        r
    }
}

// Executable implementations that mirror the specs, with proofs of equivalence.

// Insert x into sorted sequence s (executable)
fn insert_sorted_impl(s: Seq<int>, x: int) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 {
        seq![x]
    } else {
        if x <= s@[0] {
            seq![x] + s
        } else {
            seq![s@[0]] + insert_sorted_impl(s.slice(1, s.len()), x)
        }
    }
}

#[verifier(nonlinear)]
proof fn insert_sorted_impl_spec_eq(s: Seq<int>, x: int)
    ensures insert_sorted_impl(s, x) == insert_sorted_spec(s, x)
{
    if s.len() == 0 {
        // both are seq![x]
    } else {
        if x <= s@[0] {
            // both are seq![x] + s
        } else {
            insert_sorted_impl_spec_eq(s.slice(1, s.len()), x);
            // then seq![s@[0]] + ... equality follows
        }
    }
}

// Executable insertion sort that uses insert_sorted_impl
fn insertion_sort_impl(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let tail = insertion_sort_impl(s.slice(1, s.len()));
        insert_sorted_impl(tail, s@[0])
    }
}

#[verifier(nonlinear)]
proof fn insertion_sort_impl_spec_eq(s: Seq<int>)
    ensures insertion_sort_impl(s) == insertion_sort_spec(s)
{
    if s.len() == 0 {
        // both Seq::empty()
    } else {
        insertion_sort_impl_spec_eq(s.slice(1, s.len()));
        insert_sorted_impl_spec_eq(insertion_sort_impl(s.slice(1, s.len())), s@[0]);
        proof {
            let _ = insertion_sort_spec(s.slice(1, s.len()));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        s.to_multiset() == r.to_multiset(),
        is_sorted(r),
// </vc-spec>
// <vc-code>
{
    let r = insertion_sort_impl(s);
    proof {
        // Connect the executable implementation with the spec, then use the spec's postconditions.
        insertion_sort_impl_spec_eq(s);
        let spec_r = insertion_sort_spec(s);
        assert(r == spec_r);
    }
    r
}
// </vc-code>

fn main() {}

}