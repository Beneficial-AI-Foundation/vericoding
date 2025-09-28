use vstd::prelude::*;

verus! {

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }

// <vc-helpers>
use vstd::seq::*;

proof fn seq_filter_concat_preserves_multiset(old: Seq<nat>, n: nat)
    requires
        old.len() == n,
    ensures
        // concatenation of odds and evens from old equals multiset of old
        (filter(|x: nat| odd(x), old) + filter(|x: nat| even(x), old)).to_multiset() == old.to_multiset()
{
    // Proof by induction on n = old.len()
    if n == 0 {
        assert(filter(|x: nat| odd(x), old).len() == 0);
        assert(filter(|x: nat| even(x), old).len() == 0);
        assert((Seq::<nat>::empty()).to_multiset() == old.to_multiset());
    } else {
        let last_idx: int = n as int - 1;
        let prefix: Seq<nat> = old.slice(0, last_idx as usize);
        let last = old@[last_idx];
        // apply induction on prefix
        seq_filter_concat_preserves_multiset(prefix, n - 1);
        // Now reason about adding last
        if odd(last) {
            // filter odds(prefix)+[last] + filter evens(prefix) == (filter odds(prefix)+filter evens(prefix)) + [last]
            assert((filter(|x: nat| odd(x), prefix) + seq![last] + filter(|x: nat| even(x), prefix)).to_multiset()
                   == (filter(|x: nat| odd(x), prefix) + filter(|x: nat| even(x), prefix) + seq![last]).to_multiset());
            // by induction, equals prefix.multiset + {last}
            assert((filter(|x: nat| odd(x), prefix) + seq![last] + filter(|x: nat| even(x), prefix)).to_multiset()
                   == (prefix + seq![last]).to_multiset());
            assert((prefix + seq![last]).to_multiset() == old.to_multiset());
        } else {
            // last even
            assert((filter(|x: nat| odd(x), prefix) + filter(|x: nat| even(x), prefix) + seq![last]).to_multiset()
                   == (prefix + seq![last]).to_multiset());
            assert((prefix + seq![last]).to_multiset() == old.to_multiset());
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn partitionOddEven(a: &mut Vec<nat>)
    ensures 
        a@.to_multiset() == old(a)@.to_multiset(),
        !(exists|i: int, j: int| 0 <= i < j < a@.len() && even(a@[i]) && odd(a@[j])),
// </vc-spec>
// <vc-code>
{
    // Implementation: rebuild the vector by first collecting all odds, then all evens,
    // using a snapshot of the original vector `old`.
    let orig: Vec<nat> = a.clone();
    let old: Seq<nat> = a@.clone();
    let n: int = orig.len() as int;

    // Clear the original vector to rebuild it
    a.clear();

    // First pass: push all odd elements from orig preserving their original order
    let mut idx: int = 0;
    while idx < n
        invariant 0 <= idx && idx <= n;
        invariant a@.to_multiset() == filter(|x: nat| odd(x), old.slice(0, idx as usize)).to_multiset();
    {
        let v = orig[idx as usize];
        if odd(v) {
            a.push(v);
            assert(a@.to_multiset() == filter(|x: nat| odd(x), old.slice(0, (idx + 1) as usize)).to_multiset());
        } else {
            assert(a@.to_multiset() == filter(|x: nat| odd(x), old.slice(0, (idx + 1) as usize)).to_multiset());
        }
        idx += 1;
    }

    // Second pass: push all even elements from orig preserving their original order
    let mut idx2: int = 0;
    while idx2 < n
        invariant 0 <= idx2 && idx2 <= n;
        invariant a@.to_multiset() == (filter(|x: nat| odd(x), old) + filter(|x: nat| even(x), old.slice(0, idx2 as usize))).to_multiset();
    {
        let v = orig[idx2 as usize];
        if even(v) {
            a.push(v);
            assert(a@.to_multiset() == (filter(|x: nat| odd(x), old) + filter(|x: nat| even(x), old.slice(0, (idx2 + 1) as usize))).to_multiset());
        } else {
            assert(a@.to_multiset() == (filter(|x: nat| odd(x), old) + filter(|x: nat| even(x), old.slice(0, (idx2 + 1) as usize))).to_multiset());
        }
        idx2 += 1;
    }

    // Prove final multiset equality using helper lemma
    let n_nat: nat = old.len();
    proof {
        seq_filter_concat_preserves_multiset(old, n_nat);
    }
    assert(a@.to_multiset() == (filter(|x: nat| odd(x), old) + filter(|x: nat| even(x), old)).to_multiset());
    assert((filter(|x: nat| odd(x), old) + filter(|x: nat| even(x), old)).to_multiset() == old.to_multiset());
    // Thus multiset preserved
    assert(a@.to_multiset() == old.to_multiset());

    // Prove that no even occurs before an odd in resulting a
    let len_a: int = a@.len() as int;
    assert(!(exists|i: int, j: int| 0 <= i < j < len_a && even(a@[i]) && odd(a@[j])));
}
// </vc-code>

fn main() {}

}