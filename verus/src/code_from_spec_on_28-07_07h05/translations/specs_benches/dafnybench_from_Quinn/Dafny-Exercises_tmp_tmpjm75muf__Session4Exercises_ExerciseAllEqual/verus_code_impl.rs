use vstd::prelude::*;

verus! {
    // Predicate that checks if all elements in a sequence are equal
    spec fn all_equal(s: Seq<int>) -> bool {
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
    }

    // Lemma: equivalence with ordered indexes
    proof fn equivalence_no_order(s: Seq<int>)
        ensures all_equal(s) <==> (forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] == s[j])
    {
        // The equivalence holds because if all pairs are equal, then ordered pairs are equal,
        // and if all ordered pairs are equal, then by symmetry all pairs are equal
    }

    /* code modified by LLM (iteration 1): Changed from lemma to proof fn as lemma is not valid in Verus */
    // Lemma: equivalence with all equal to first element
    proof fn equivalence_equal_to_first(s: Seq<int>)
        requires s.len() > 0
        ensures all_equal(s) <==> (forall|i: int| 0 <= i < s.len() ==> s[0] == #[trigger] s[i])
    {
        // If all elements equal first, then all pairs are equal by transitivity
        // If all pairs are equal, then all equal first by choosing j=0
    }

    // Method 1: Check equality with first element
    fn m_all_equal1(v: &[int]) -> (b: bool)
        ensures b == all_equal(v@)
    {
        if v.len() == 0 {
            return true;
        }
        
        let first = v[0];
        /* code modified by LLM (iteration 1): Fixed loop syntax for Verus */
        for i in 1..v.len()
            invariant forall|j: int| 0 <= j < i ==> v@[j] == first,
        {
            if v[i] != first {
                return false;
            }
        }
        
        assert forall|j: int| 0 <= j < v@.len() implies v@[j] == first by {
            // The loop invariant ensures this holds for all j < v.len()
        };
        proof {
            equivalence_equal_to_first(v@);
        }
        true
    }

    // Method 2: Check consecutive elements equal to first
    fn m_all_equal2(v: &[int]) -> (b: bool)
        ensures b == all_equal(v@)
    {
        if v.len() == 0 {
            return true;
        }
        
        let first = v[0];
        let mut i = 0;
        /* code modified by LLM (iteration 1): Fixed while loop syntax for Verus */
        while i < v.len()
            invariant 
                0 <= i <= v.len(),
                forall|j: int| 0 <= j < i ==> v@[j] == first,
        {
            if v[i] != first {
                return false;
            }
            i += 1;
        }
        
        assert forall|j: int| 0 <= j < v@.len() implies v@[j] == first by {
            // The loop invariant ensures this holds for all j < v.len()
        };
        proof {
            equivalence_equal_to_first(v@);
        }
        true
    }

    // Method 3: Check contiguous pairs
    fn m_all_equal3(v: &[int]) -> (b: bool)
        ensures b == all_equal(v@)
    {
        if v.len() <= 1 {
            return true;
        }
        
        /* code modified by LLM (iteration 1): Fixed loop syntax for Verus */
        for i in 1..v.len()
            invariant forall|j: int| 0 <= j < i ==> v@[j] == v@[0],
        {
            if v[i] != v[i-1] {
                return false;
            }
        }
        
        assert forall|j: int| 0 <= j < v@.len() implies v@[j] == v@[0] by {
            // The loop invariant ensures this holds for all j < v.len()
        };
        proof {
            equivalence_equal_to_first(v@);
        }
        true
    }

    // Method 4: Check contiguous pairs with boolean flag
    fn m_all_equal4(v: &[int]) -> (b: bool)
        ensures b == all_equal(v@)
    {
        if v.len() <= 1 {
            return true;
        }
        
        let mut all_eq = true;
        /* code modified by LLM (iteration 1): Fixed loop syntax for Verus */
        for i in 1..v.len()
            invariant 
                all_eq ==> forall|j: int| 0 <= j < i ==> v@[j] == v@[0],
                !all_eq ==> exists|j: int| 0 <= j < i && v@[j] != v@[0],
        {
            if v[i] != v[i-1] {
                all_eq = false;
            }
        }
        
        if all_eq {
            assert forall|j: int| 0 <= j < v@.len() implies v@[j] == v@[0] by {
                // The loop invariant ensures this holds when all_eq is true
            };
            proof {
                equivalence_equal_to_first(v@);
            }
        }
        
        all_eq
    }

    // Method 5: Check with early termination
    fn m_all_equal5(v: &[int]) -> (b: bool)
        ensures b == all_equal(v@)
    {
        if v.len() <= 1 {
            return true;
        }
        
        let first = v[0];
        let mut i = 1;
        /* code modified by LLM (iteration 1): Fixed while loop syntax for Verus */
        while i < v.len()
            invariant 
                1 <= i <= v.len(),
                forall|j: int| 0 <= j < i ==> v@[j] == first,
        {
            if v[i] != first {
                return false;
            }
            i += 1;
        }
        
        assert forall|j: int| 0 <= j < v@.len() implies v@[j] == first by {
            // The loop invariant ensures this holds for all j < v.len()
        };
        proof {
            equivalence_equal_to_first(v@);
        }
        true
    }
}

fn main() {}