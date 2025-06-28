use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nomultiples(u: Seq<nat>) -> bool {
    forall|j: int, k: int| 0 <= j < k < u.len() ==> u.spec_index(j) != u.spec_index(k)
}

spec fn bullspec(s: Seq<nat>, u: Seq<nat>) -> nat {
    count_bulls(s, u, 0)
}

spec fn count_bulls(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases u.len() - i
{
    if i >= u.len() {
        0
    } else {
        let rest = count_bulls(s, u, i + 1);
        if s.spec_index(i) == u.spec_index(i) {
            rest + 1
        } else {
            rest
        }
    }
}

spec fn cowspec(s: Seq<nat>, u: Seq<nat>) -> nat {
    count_cows(s, u, 0)
}

spec fn count_cows(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases u.len() - i
{
    if i >= u.len() {
        0
    } else {
        let rest = count_cows(s, u, i + 1);
        if s.spec_index(i) != u.spec_index(i) && contains_at_different_pos(u, s.spec_index(i), i) {
            rest + 1
        } else {
            rest
        }
    }
}

spec fn contains_at_different_pos(u: Seq<nat>, val: nat, exclude_pos: int) -> bool {
    exists|j: int| 0 <= j < u.len() && j != exclude_pos && u.spec_index(j) == val
}

// Helper spec function to count bulls from start up to position i (exclusive)
spec fn bulls_up_to(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases i
{
    if i <= 0 {
        0
    } else {
        let rest = bulls_up_to(s, u, i - 1);
        if s.spec_index(i - 1) == u.spec_index(i - 1) {
            rest + 1
        } else {
            rest
        }
    }
}

// Helper spec function to count cows from start up to position i (exclusive)
spec fn cows_up_to(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases i
{
    if i <= 0 {
        0
    } else {
        let rest = cows_up_to(s, u, i - 1);
        if s.spec_index(i - 1) != u.spec_index(i - 1) && contains_at_different_pos(u, s.spec_index(i - 1), i - 1) {
            rest + 1
        } else {
            rest
        }
    }
}

// Helper function to check if a value exists at a different position
fn contains_different_pos(u: Seq<nat>, val: nat, exclude_pos: usize) -> (result: bool)
    requires exclude_pos < u.len()
    ensures result == contains_at_different_pos(u, val, exclude_pos as int)
{
    let mut j = 0;
    while j < u.len()
        invariant
            0 <= j <= u.len(),
            forall|k: int| 0 <= k < j && k != exclude_pos as int ==> u.spec_index(k) != val
    {
        if j != exclude_pos && u[j] == val {
            return true;
        }
        j = j + 1;
    }
    false
}

// Simplified lemma for bulls relationship
proof fn lemma_bulls_equivalence(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures bulls_up_to(s, u, s.len() as int) == bullspec(s, u)
    decreases s.len()
{
    if s.len() == 0 {
        assert(bulls_up_to(s, u, 0) == 0);
        assert(count_bulls(s, u, 0) == 0);
    } else {
        let n = s.len() as int;
        lemma_bulls_step(s, u, n - 1);
    }
}

// Simplified lemma for cows relationship  
proof fn lemma_cows_equivalence(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures cows_up_to(s, u, s.len() as int) == cowspec(s, u)
    decreases s.len()
{
    if s.len() == 0 {
        assert(cows_up_to(s, u, 0) == 0);
        assert(count_cows(s, u, 0) == 0);
    } else {
        let n = s.len() as int;
        lemma_cows_step(s, u, n - 1);
    }
}

proof fn lemma_bulls_step(s: Seq<nat>, u: Seq<nat>, i: int)
    requires 
        s.len() == u.len(),
        0 <= i < s.len()
    ensures 
        bulls_up_to(s, u, i + 1) == bulls_up_to(s, u, i) + (if s.spec_index(i) == u.spec_index(i) { 1 } else { 0 }),
        count_bulls(s, u, i) == count_bulls(s, u, i + 1) + (if s.spec_index(i) == u.spec_index(i) { 1 } else { 0 })
{
    // These follow directly from the definitions
}

proof fn lemma_cows_step(s: Seq<nat>, u: Seq<nat>, i: int)
    requires 
        s.len() == u.len(),
        0 <= i < s.len()
    ensures 
        cows_up_to(s, u, i + 1) == cows_up_to(s, u, i) + (if s.spec_index(i) != u.spec_index(i) && contains_at_different_pos(u, s.spec_index(i), i) { 1 } else { 0 }),
        count_cows(s, u, i) == count_cows(s, u, i + 1) + (if s.spec_index(i) != u.spec_index(i) && contains_at_different_pos(u, s.spec_index(i), i) { 1 } else { 0 })
{
    // These follow directly from the definitions
}

// Main lemma to establish the relationship
proof fn lemma_count_relationship(s: Seq<nat>, u: Seq<nat>, i: int)
    requires s.len() == u.len(), 0 <= i <= s.len()
    ensures 
        bulls_up_to(s, u, i) + count_bulls(s, u, i) == bullspec(s, u),
        cows_up_to(s, u, i) + count_cows(s, u, i) == cowspec(s, u)
    decreases i
{
    if i == 0 {
        assert(bulls_up_to(s, u, 0) == 0);
        assert(cows_up_to(s, u, 0) == 0);
        assert(count_bulls(s, u, 0) == bullspec(s, u));
        assert(count_cows(s, u, 0) == cowspec(s, u));
    } else if i == s.len() {
        assert(count_bulls(s, u, s.len() as int) == 0);
        assert(count_cows(s, u, s.len() as int) == 0);
        lemma_bulls_equivalence(s, u);
        lemma_cows_equivalence(s, u);
    } else {
        lemma_count_relationship(s, u, i - 1);
        lemma_bulls_step(s, u, i - 1);
        lemma_cows_step(s, u, i - 1);
    }
}

fn BullsCows(s: Seq<nat>, u: Seq<nat>) -> (b: nat, c: nat)
    requires
        0 < u.len() == s.len() <= 10,
        nomultiples(u) && nomultiples(s)
    ensures
        b >= 0 && c >= 0,
        b == bullspec(s, u),
        c == cowspec(s, u)
{
    let mut bulls = 0;
    let mut cows = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == u.len(),
            bulls == bulls_up_to(s, u, i as int),
            cows == cows_up_to(s, u, i as int)
    {
        if s[i] == u[i] {
            bulls = bulls + 1;
            
            proof {
                assert(s.spec_index(i as int) == u.spec_index(i as int));
                assert(bulls_up_to(s, u, (i + 1) as int) == bulls_up_to(s, u, i as int) + 1);
            }
        } else {
            // Check if s[i] appears in u at a different position
            let found = contains_different_pos(u, s[i], i);
            
            if found {
                cows = cows + 1;
                
                proof {
                    assert(s.spec_index(i as int) != u.spec_index(i as int));
                    assert(contains_at_different_pos(u, s.spec_index(i as int), i as int));
                    assert(cows_up_to(s, u, (i + 1) as int) == cows_up_to(s, u, i as int) + 1);
                }
            } else {
                proof {
                    assert(s.spec_index(i as int) != u.spec_index(i as int));
                    assert(!contains_at_different_pos(u, s.spec_index(i as int), i as int));
                    assert(cows_up_to(s, u, (i + 1) as int) == cows_up_to(s, u, i as int));
                }
            }
            
            proof {
                assert(bulls_up_to(s, u, (i + 1) as int) == bulls_up_to(s, u, i as int));
            }
        }
        i = i + 1;
    }
    
    // Prove final relationship using the main lemma
    proof {
        lemma_count_relationship(s, u, s.len() as int);
    }
    
    (bulls, cows)
}

}