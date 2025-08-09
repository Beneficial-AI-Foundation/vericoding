use vstd::prelude::*;

verus! {
    // Helper function to create a set of elements less than threshold
    spec fn set_less_than(numbers: Set<int>, threshold: int) -> Set<int> {
        numbers.filter(|i: int| i < threshold)
    }

    // Lemma helper for set cardinality - simplified version
    proof fn set_membership_implies_cardinality_helper<A>(s: Set<A>, t: Set<A>, s_size: nat)
        requires
            s_size == s.len(),
            s.finite(),
            t.finite(),
            forall|x: A| s.contains(x) <==> t.contains(x),
        ensures s.len() == t.len()
        decreases s_size
    {
        // If two sets have identical membership, they have the same cardinality
        // This follows from the extensionality of sets in Verus
        assert(s =~= t) by {
            assert(forall|x: A| s.contains(x) <==> t.contains(x));
        }
    }

    // Main lemma for set cardinality
    proof fn set_membership_implies_cardinality<A>(s: Set<A>, t: Set<A>)
        requires 
            s.finite(),
            t.finite(),
            forall|x: A| s.contains(x) <==> t.contains(x),
        ensures s.len() == t.len()
    {
        set_membership_implies_cardinality_helper(s, t, s.len());
    }

    // Set equality lemma helper
    proof fn set_membership_implies_equality_helper<A>(s: Set<A>, t: Set<A>, s_size: nat)
        requires
            s_size == s.len(),
            s.finite(),
            t.finite(),
            forall|x: A| s.contains(x) <==> t.contains(x),
        ensures s == t
        decreases s_size
    {
        // Two sets are equal if they have identical membership
        // This is the definition of set extensionality
        assert(s =~= t) by {
            assert(forall|x: A| s.contains(x) <==> t.contains(x));
        }
    }

    // Set equality lemma
    proof fn set_membership_implies_equality<A>(s: Set<A>, t: Set<A>)
        requires 
            s.finite(),
            t.finite(),
            forall|x: A| s.contains(x) <==> t.contains(x),
        ensures s == t
    {
        set_membership_implies_equality_helper(s, t, s.len());
    }

    // Sorted sequence predicates
    spec fn sorted_seq(a: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
    }

    spec fn sorted(a: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
    }

    spec fn distinct(a: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j ==> a[i] != a[j]
    }

    spec fn sorted_eq(a: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    }

    spec fn less_than(a: Seq<int>, key: int) -> bool {
        forall|i: int| 0 <= i < a.len() ==> a[i] < key
    }

    spec fn greater_than(a: Seq<int>, key: int) -> bool {
        forall|i: int| 0 <= i < a.len() ==> a[i] > key
    }

    spec fn greater_equal_than(a: Seq<int>, key: int) -> bool {
        forall|i: int| 0 <= i < a.len() ==> a[i] >= key
    }

    // Count function for boolean sequences
    spec fn count(a: Seq<bool>) -> nat
        decreases a.len()
    {
        if a.len() == 0 {
            0nat
        } else {
            (if a[0] { 1nat } else { 0nat }) + count(a.subrange(1, a.len() as int))
        }
    }

    // Distributive lemma for sequences
    proof fn distributive_in(a: Seq<int>, b: Seq<int>, k: int, key: int)
        requires
            a.len() + 1 == b.len(),
            0 <= k <= a.len(),
            b =~= a.subrange(0, k).add(seq![key]).add(a.subrange(k, a.len() as int)),
        ensures
            forall|i: int| 0 <= i < a.len() ==> b.contains(a[i]),
    {
        // Show that every element of a is contained in b
        assert(forall|i: int| 0 <= i < a.len() ==> b.contains(a[i])) by {
            assert(forall|i: int| 0 <= i < k ==> {
                &&& a[i] == a.subrange(0, k)[i]
                &&& a.subrange(0, k).contains(a[i])
                &&& b.contains(a[i])
            });
            assert(forall|i: int| k <= i < a.len() ==> {
                &&& a[i] == a.subrange(k, a.len() as int)[i - k]
                &&& a.subrange(k, a.len() as int).contains(a[i])
                &&& b.contains(a[i])
            });
        }
    }

    // Distributive greater lemma
    proof fn distributive_greater(a: Seq<int>, b: Seq<int>, k: int, key: int)
        requires
            a.len() + 1 == b.len(),
            0 <= k <= a.len(),
            b =~= a.subrange(0, k).add(seq![key]).add(a.subrange(k, a.len() as int)),
            forall|j: int| 0 <= j < a.len() ==> a[j] > 0,
            key > 0,
        ensures
            forall|i: int| 0 <= i < b.len() ==> b[i] > 0,
    {
        // Show that all elements in b are positive
        assert(forall|i: int| 0 <= i < b.len() ==> b[i] > 0) by {
            // Elements from first part of a
            assert(forall|i: int| 0 <= i < k ==> {
                &&& b[i] == a.subrange(0, k)[i]
                &&& b[i] == a[i]
                &&& b[i] > 0
            });
            
            // The inserted key
            assert(b[k] == key && key > 0);
            
            // Elements from second part of a
            assert(forall|i: int| k + 1 <= i < b.len() ==> {
                &&& b[i] == a.subrange(k, a.len() as int)[i - k - 1]
                &&& b[i] == a[i - 1]
                &&& b[i] > 0
            });
        }
    }
}

fn main() {
}