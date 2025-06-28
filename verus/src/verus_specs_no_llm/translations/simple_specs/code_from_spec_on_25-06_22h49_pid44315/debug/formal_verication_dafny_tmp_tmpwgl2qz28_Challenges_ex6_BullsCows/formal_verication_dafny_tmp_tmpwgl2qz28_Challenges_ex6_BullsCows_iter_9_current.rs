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
            assert(u.spec_index(j as int) == val);
            assert(j as int != exclude_pos as int);
            assert(0 <= j as int < u.len());
            return true;
        }
        j = j + 1;
    }
    
    // Prove that no element at different position equals val
    assert(forall|k: int| 0 <= k < u.len() && k != exclude_pos as int ==> u.spec_index(k) != val);
    false
}

// Lemma to establish the relationship between forward and backward counting
proof fn lemma_bulls_equivalence(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures bulls_up_to(s, u, s.len() as int) == bullspec(s, u)
{
    lemma_bulls_forward_backward(s, u, 0, s.len() as int);
}

proof fn lemma_cows_equivalence(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures cows_up_to(s, u, s.len() as int) == cowspec(s, u)
{
    lemma_cows_forward_backward(s, u, 0, s.len() as int);
}

proof fn lemma_bulls_forward_backward(s: Seq<nat>, u: Seq<nat>, start: int, end: int)
    requires 
        s.len() == u.len(),
        0 <= start <= end <= s.len()
    ensures 
        bulls_up_to(s, u, end) - bulls_up_to(s, u, start) == count_bulls(s, u, start) - count_bulls(s, u, end)
    decreases end - start
{
    if start >= end {
        // Base case
    } else {
        let mid = start + 1;
        lemma_bulls_forward_backward(s, u, start, mid);
        lemma_bulls_forward_backward(s, u, mid, end);
        
        // The key insight: both functions count the same elements, just in different directions
        if s.spec_index(start) == u.spec_index(start) {
            assert(bulls_up_to(s, u, mid) == bulls_up_to(s, u, start) + 1);
            assert(count_bulls(s, u, start) == count_bulls(s, u, mid) + 1);
        } else {
            assert(bulls_up_to(s, u, mid) == bulls_up_to(s, u, start));
            assert(count_bulls(s, u, start) == count_bulls(s, u, mid));
        }
    }
}

proof fn lemma_cows_forward_backward(s: Seq<nat>, u: Seq<nat>, start: int, end: int)
    requires 
        s.len() == u.len(),
        0 <= start <= end <= s.len()
    ensures 
        cows_up_to(s, u, end) - cows_up_to(s, u, start) == count_cows(s, u, start) - count_cows(s, u, end)
    decreases end - start
{
    if start >= end {
        // Base case
    } else {
        let mid = start + 1;
        lemma_cows_forward_backward(s, u, start, mid);
        lemma_cows_forward_backward(s, u, mid, end);
        
        // The key insight: both functions count the same elements, just in different directions
        if s.spec_index(start) != u.spec_index(start) && contains_at_different_pos(u, s.spec_index(start), start) {
            assert(cows_up_to(s, u, mid) == cows_up_to(s, u, start) + 1);
            assert(count_cows(s, u, start) == count_cows(s, u, mid) + 1);
        } else {
            assert(cows_up_to(s, u, mid) == cows_up_to(s, u, start));
            assert(count_cows(s, u, start) == count_cows(s, u, mid));
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
    
    // Prove final relationship using the lemmas
    proof {
        lemma_bulls_equivalence(s, u);
        lemma_cows_equivalence(s, u);
    }
    
    (bulls, cows)
}

}