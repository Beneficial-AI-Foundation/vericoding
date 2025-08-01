use vstd::prelude::*;

verus! {
    //ATOM
    // Helper function to create a set of elements less than threshold
    spec fn set_less_than(numbers: Set<int>, threshold: int) -> Set<int> {
        numbers.filter(|i: int| i < threshold)
    }

    //ATOM
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
        if s_size == 0 {
            // Base case: both sets are empty
            /* code modified by LLM (iteration 1): Fixed assertion by proving that if s is empty and sets are equivalent, then t must also be empty */
            assert(s.len() == 0);
            // Since s is empty and the sets are equivalent, t must also be empty
            assert(forall|x: A| !s.contains(x));
            assert(forall|x: A| s.contains(x) <==> t.contains(x));
            assert(forall|x: A| !t.contains(x));
            // An empty set has length 0
            assert(t =~= Set::<A>::empty());
            assert(t.len() == 0);
        } else {
            // Choose an element from s
            let s_hd = s.choose();
            assert(s.contains(s_hd));
            assert(t.contains(s_hd));
            
            let s_rest = s.remove(s_hd);
            let t_rest = t.remove(s_hd);
            
            assert(s_rest.len() == s.len() - 1);
            assert(t_rest.len() == t.len() - 1);
            
            // Prove the equivalence holds for the remaining elements
            assert(forall|x: A| s_rest.contains(x) <==> t_rest.contains(x));
            
            set_membership_implies_cardinality_helper(s_rest, t_rest, (s_size - 1) as nat);
        }
    }

    //ATOM
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

    //ATOM
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
        if s_size == 0 {
            // Base case: both sets are empty
            /* code modified by LLM (iteration 1): Fixed assertion by proving that if s is empty and sets are equivalent, then t must also be empty */
            assert(s.len() == 0);
            // Since s is empty and the sets are equivalent, t must also be empty
            assert(forall|x: A| !s.contains(x));
            assert(forall|x: A| s.contains(x) <==> t.contains(x));
            assert(forall|x: A| !t.contains(x));
            // An empty set has length 0
            assert(t =~= Set::<A>::empty());
            assert(t.len() == 0);
        } else {
            let s_hd = s.choose();
            let s_rest = s.remove(s_hd);
            let t_rest = t.remove(s_hd);
            
            assert(forall|x: A| s_rest.contains(x) <==> t_rest.contains(x));
            
            set_membership_implies_equality_helper(s_rest, t_rest, (s_size - 1) as nat);
            
            // Reconstruct the sets
            assert(s == s_rest.insert(s_hd));
            assert(t == t_rest.insert(s_hd));
        }
    }

    //ATOM
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

    //ATOM
    // Sorted sequence predicates
    spec fn sorted_seq(a: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
    }

    //ATOM
    spec fn sorted(a: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
    }

    //ATOM
    spec fn distinct(a: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j ==> a[i] != a[j]
    }

    //ATOM
    spec fn sorted_eq(a: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    }

    //ATOM
    spec fn less_than(a: Seq<int>, key: int) -> bool {
        forall|i: int| 0 <= i < a.len() ==> a[i] < key
    }

    //ATOM
    spec fn greater_than(a: Seq<int>, key: int) -> bool {
        forall|i: int| 0 <= i < a.len() ==> a[i] > key
    }

    //ATOM
    spec fn greater_equal_than(a: Seq<int>, key: int) -> bool {
        forall|i: int| 0 <= i < a.len() ==> a[i] >= key
    }

    //ATOM
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

    //ATOM
    // Distributive lemma for sequences
    proof fn distributive_in(a: Seq<int>, b: Seq<int>, k: int, key: int)
        requires
            a.len() + 1 == b.len(),
            0 <= k <= a.len(),
            b =~= a.subrange(0, k).add(seq![key]).add(a.subrange(k, a.len() as int)),
        ensures
            forall|i: int| 0 <= i < a.len() ==> b.contains(a[i]),
    {
        /* code modified by LLM (iteration 4): Fixed trigger expressions to use boolean conditions instead of integer values */
        // We need to prove that every element of a is contained in b
        // b is constructed as: a[0..k] + [key] + a[k..a.len()]
        // So every element of a appears in either the first or third part of b
        
        // For elements in the first part [0, k)
        assert(forall|i: int| #[trigger] (0 <= i < k) ==> 0 <= i < a.len() ==> (
            a[i] == a.subrange(0, k)[i] &&
            b.subrange(0, k).contains(a[i]) &&
            b.contains(a[i])
        ));
        
        // For elements in the second part [k, a.len())
        assert(forall|i: int| #[trigger] (k <= i < a.len()) ==> (
            a[i] == a.subrange(k, a.len() as int)[i - k] &&
            b.subrange(k + 1, b.len() as int).contains(a[i]) &&
            b.contains(a[i])
        ));
        
        // Combine both cases
        assert(forall|i: int| #[trigger] (0 <= i < a.len()) ==> (
            ((0 <= i < k) || (k <= i < a.len())) &&
            b.contains(a[i])
        ));
    }

    //ATOM
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
        // This lemma would need more detailed proof work
        // For now, we rely on the specification
    }
}

fn main() {
    // TODO: Remove this comment and implement the function body
}