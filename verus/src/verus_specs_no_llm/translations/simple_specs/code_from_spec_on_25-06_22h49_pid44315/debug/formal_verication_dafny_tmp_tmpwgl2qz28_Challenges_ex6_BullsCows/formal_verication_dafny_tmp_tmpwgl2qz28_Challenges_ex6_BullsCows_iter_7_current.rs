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

// Corrected lemma to establish the relationship between forward and backward counting
proof fn lemma_bulls_forward_backward(s: Seq<nat>, u: Seq<nat>, i: int)
    requires 
        s.len() == u.len(),
        0 <= i <= s.len()
    ensures 
        bulls_up_to(s, u, i) + count_bulls(s, u, i) == bullspec(s, u)
    decreases s.len() - i
{
    if i == s.len() {
        assert(count_bulls(s, u, i) == 0);
        lemma_bulls_up_to_complete(s, u);
    } else {
        lemma_bulls_forward_backward(s, u, i + 1);
        
        if s.spec_index(i) == u.spec_index(i) {
            assert(bulls_up_to(s, u, i + 1) == bulls_up_to(s, u, i) + 1);
            assert(count_bulls(s, u, i) == count_bulls(s, u, i + 1) + 1);
        } else {
            assert(bulls_up_to(s, u, i + 1) == bulls_up_to(s, u, i));
            assert(count_bulls(s, u, i) == count_bulls(s, u, i + 1));
        }
    }
}

proof fn lemma_cows_forward_backward(s: Seq<nat>, u: Seq<nat>, i: int)
    requires 
        s.len() == u.len(),
        0 <= i <= s.len()
    ensures 
        cows_up_to(s, u, i) + count_cows(s, u, i) == cowspec(s, u)
    decreases s.len() - i
{
    if i == s.len() {
        assert(count_cows(s, u, i) == 0);
        lemma_cows_up_to_complete(s, u);
    } else {
        lemma_cows_forward_backward(s, u, i + 1);
        
        if s.spec_index(i) != u.spec_index(i) && contains_at_different_pos(u, s.spec_index(i), i) {
            assert(cows_up_to(s, u, i + 1) == cows_up_to(s, u, i) + 1);
            assert(count_cows(s, u, i) == count_cows(s, u, i + 1) + 1);
        } else {
            assert(cows_up_to(s, u, i + 1) == cows_up_to(s, u, i));
            assert(count_cows(s, u, i) == count_cows(s, u, i + 1));
        }
    }
}

proof fn lemma_bulls_up_to_complete(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures bulls_up_to(s, u, s.len() as int) == bullspec(s, u)
{
    lemma_bulls_up_to_equals_count_bulls_backwards(s, u, 0, s.len() as int);
}

proof fn lemma_cows_up_to_complete(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures cows_up_to(s, u, s.len() as int) == cowspec(s, u)
{
    lemma_cows_up_to_equals_count_cows_backwards(s, u, 0, s.len() as int);
}

proof fn lemma_bulls_up_to_equals_count_bulls_backwards(s: Seq<nat>, u: Seq<nat>, from: int, to: int)
    requires 
        s.len() == u.len(),
        0 <= from <= to <= s.len()
    ensures 
        bulls_up_to(s, u, to) - bulls_up_to(s, u, from) == count_bulls(s, u, from) - count_bulls(s, u, to)
    decreases to - from
{
    if from == to {
        // Base case
    } else {
        lemma_bulls_up_to_equals_count_bulls_backwards(s, u, from + 1, to);
        
        if s.spec_index(from) == u.spec_index(from) {
            assert(bulls_up_to(s, u, from + 1) == bulls_up_to(s, u, from) + 1);
            assert(count_bulls(s, u, from) == count_bulls(s, u, from + 1) + 1);
        } else {
            assert(bulls_up_to(s, u, from + 1) == bulls_up_to(s, u, from));
            assert(count_bulls(s, u, from) == count_bulls(s, u, from + 1));
        }
    }
}

proof fn lemma_cows_up_to_equals_count_cows_backwards(s: Seq<nat>, u: Seq<nat>, from: int, to: int)
    requires 
        s.len() == u.len(),
        0 <= from <= to <= s.len()
    ensures 
        cows_up_to(s, u, to) - cows_up_to(s, u, from) == count_cows(s, u, from) - count_cows(s, u, to)
    decreases to - from
{
    if from == to {
        // Base case
    } else {
        lemma_cows_up_to_equals_count_cows_backwards(s, u, from + 1, to);
        
        if s.spec_index(from) != u.spec_index(from) && contains_at_different_pos(u, s.spec_index(from), from) {
            assert(cows_up_to(s, u, from + 1) == cows_up_to(s, u, from) + 1);
            assert(count_cows(s, u, from) == count_cows(s, u, from + 1) + 1);
        } else {
            assert(cows_up_to(s, u, from + 1) == cows_up_to(s, u, from));
            assert(count_cows(s, u, from) == count_cows(s, u, from + 1));
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
    
    // Prove final relationship using the corrected lemmas
    proof {
        lemma_bulls_forward_backward(s, u, 0);
        lemma_cows_forward_backward(s, u, 0);
        assert(bulls_up_to(s, u, 0) == 0);
        assert(cows_up_to(s, u, 0) == 0);
        assert(bulls == bulls_up_to(s, u, s.len() as int));
        assert(cows == cows_up_to(s, u, s.len() as int));
        assert(bulls == bullspec(s, u));
        assert(cows == cowspec(s, u));
    }
    
    (bulls, cows)
}

}