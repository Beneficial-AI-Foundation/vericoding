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
        // and if all ordered pairs are equal, then all pairs are equal by symmetry
        assert(all_equal(s) ==> (forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] == s[j]));
        assert((forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] == s[j]) ==> all_equal(s)) by {
            if forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] == s[j] {
                assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() implies s[i] == s[j] by {
                    if i <= j {
                        assert(s[i] == s[j]);
                    } else {
                        assert(s[j] == s[i]);
                        assert(s[i] == s[j]);
                    }
                };
            }
        };
    }

    // Lemma: equivalence with all equal to first element
    proof fn equivalence_equal_to_first(s: Seq<int>)
        requires s.len() > 0
        ensures all_equal(s) <==> (forall|i: int| 0 <= i < s.len() ==> s[0] == #[trigger] s[i])
    {
        // If all elements equal first, then all elements are equal
        assert((forall|i: int| 0 <= i < s.len() ==> s[0] == s[i]) ==> all_equal(s)) by {
            if forall|i: int| 0 <= i < s.len() ==> s[0] == s[i] {
                assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() implies s[i] == s[j] by {
                    assert(s[0] == s[i]);
                    assert(s[0] == s[j]);
                    assert(s[i] == s[j]);
                };
            }
        };
        // If all elements are equal, then all equal first element
        assert(all_equal(s) ==> (forall|i: int| 0 <= i < s.len() ==> s[0] == s[i]));
    }

    // Method 1: Check equality with first element
    fn m_all_equal1(v: &[int]) -> (b: bool)
        ensures b == all_equal(v@)
    {
        if v.len() == 0 {
            return true;
        }
        
        let first = v[0];
        for i in 1..v.len()
            invariant forall|k: int| 0 <= k < i ==> v@[0] == v@[k]
        {
            if v[i] != first {
                return false;
            }
        }
        
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
        
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                forall|k: int| 0 <= k < i ==> v@[0] == v@[k]
        {
            if v[i] != first {
                return false;
            }
            i += 1;
        }
        
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
        
        for i in 0..v.len() - 1
            invariant forall|k: int| 0 <= k < i ==> v@[k] == v@[k + 1]
        {
            if v[i] != v[i + 1] {
                return false;
            }
        }
        
        // Prove that consecutive equality implies all equal
        proof {
            assert forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() implies v@[i] == v@[j] by {
                if i <= j {
                    /* code modified by LLM (iteration 1): changed loop variable from int to usize to fix += operator usage */
                    let mut k: usize = i as usize;
                    while k < j as usize
                        invariant
                            i <= k <= j,
                            v@[i] == v@[k as int]
                    {
                        assert(v@[k as int] == v@[k as int + 1]);
                        k += 1;
                    }
                } else {
                    /* code modified by LLM (iteration 1): changed loop variable from int to usize to fix += operator usage */
                    let mut k: usize = j as usize;
                    while k < i as usize
                        invariant
                            j <= k <= i,
                            v@[j] == v@[k as int]
                    {
                        assert(v@[k as int] == v@[k as int + 1]);
                        k += 1;
                    }
                }
            };
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
        
        let mut all_same = true;
        
        for i in 0..v.len() - 1
            invariant all_same <==> (forall|k: int| 0 <= k < i ==> v@[k] == v@[k + 1])
        {
            if v[i] != v[i + 1] {
                all_same = false;
            }
        }
        
        if !all_same {
            return false;
        }
        
        // Prove that consecutive equality implies all equal
        proof {
            assert forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() implies v@[i] == v@[j] by {
                if i <= j {
                    /* code modified by LLM (iteration 1): changed loop variable from int to usize to fix += operator usage */
                    let mut k: usize = i as usize;
                    while k < j as usize
                        invariant
                            i <= k <= j,
                            v@[i] == v@[k as int]
                    {
                        assert(v@[k as int] == v@[k as int + 1]);
                        k += 1;
                    }
                } else {
                    /* code modified by LLM (iteration 1): changed loop variable from int to usize to fix += operator usage */
                    let mut k: usize = j as usize;
                    while k < i as usize
                        invariant
                            j <= k <= i,
                            v@[j] == v@[k as int]
                    {
                        assert(v@[k as int] == v@[k as int + 1]);
                        k += 1;
                    }
                }
            };
        }
        
        true
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
        
        while i < v.len()
            invariant
                1 <= i <= v.len(),
                forall|k: int| 0 <= k < i ==> v@[0] == v@[k]
        {
            if v[i] != first {
                // Early termination case
                proof {
                    assert(v@[0] != v@[i as int]);
                    assert(!all_equal(v@));
                }
                return false;
            }
            i += 1;
        }
        
        proof {
            equivalence_equal_to_first(v@);
        }
        
        true
    }
}

fn main() {}