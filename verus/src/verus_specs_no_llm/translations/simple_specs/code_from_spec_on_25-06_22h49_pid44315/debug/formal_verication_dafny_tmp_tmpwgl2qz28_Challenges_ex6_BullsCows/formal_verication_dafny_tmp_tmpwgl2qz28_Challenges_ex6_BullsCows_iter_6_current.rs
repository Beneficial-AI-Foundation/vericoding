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

// Lemma to prove the relationship between counting functions
proof fn lemma_count_relationship(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures 
        bulls_up_to(s, u, s.len() as int) == bullspec(s, u),
        cows_up_to(s, u, s.len() as int) == cowspec(s, u)
{
    lemma_bulls_equivalence(s, u, s.len() as int);
    lemma_cows_equivalence(s, u, s.len() as int);
}

proof fn lemma_bulls_equivalence(s: Seq<nat>, u: Seq<nat>, n: int)
    requires 
        0 <= n <= s.len(),
        s.len() == u.len()
    ensures 
        bulls_up_to(s, u, n) == bullspec(s, u) - count_bulls(s, u, n)
    decreases n
{
    if n == 0 {
        assert(bulls_up_to(s, u, 0) == 0);
        assert(count_bulls(s, u, 0) == bullspec(s, u));
    } else {
        lemma_bulls_equivalence(s, u, n - 1);
        
        if s.spec_index(n - 1) == u.spec_index(n - 1) {
            assert(bulls_up_to(s, u, n) == bulls_up_to(s, u, n - 1) + 1);
            assert(count_bulls(s, u, n - 1) == count_bulls(s, u, n) + 1);
        } else {
            assert(bulls_up_to(s, u, n) == bulls_up_to(s, u, n - 1));
            assert(count_bulls(s, u, n - 1) == count_bulls(s, u, n));
        }
    }
}

proof fn lemma_cows_equivalence(s: Seq<nat>, u: Seq<nat>, n: int)
    requires 
        0 <= n <= s.len(),
        s.len() == u.len()
    ensures 
        cows_up_to(s, u, n) == cowspec(s, u) - count_cows(s, u, n)
    decreases n
{
    if n == 0 {
        assert(cows_up_to(s, u, 0) == 0);
        assert(count_cows(s, u, 0) == cowspec(s, u));
    } else {
        lemma_cows_equivalence(s, u, n - 1);
        
        if s.spec_index(n - 1) != u.spec_index(n - 1) && contains_at_different_pos(u, s.spec_index(n - 1), n - 1) {
            assert(cows_up_to(s, u, n) == cows_up_to(s, u, n - 1) + 1);
            assert(count_cows(s, u, n - 1) == count_cows(s, u, n) + 1);
        } else {
            assert(cows_up_to(s, u, n) == cows_up_to(s, u, n - 1));
            assert(count_cows(s, u, n - 1) == count_cows(s, u, n));
        }
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
        } else {
            // Check if s[i] appears in u at a different position
            let found = contains_different_pos(u, s[i], i);
            
            if found {
                cows = cows + 1;
            }
        }
        i = i + 1;
    }
    
    // Prove final relationship
    proof {
        lemma_count_relationship(s, u);
        assert(bulls == bullspec(s, u));
        assert(cows == cowspec(s, u));
    }
    
    (bulls, cows)
}

}