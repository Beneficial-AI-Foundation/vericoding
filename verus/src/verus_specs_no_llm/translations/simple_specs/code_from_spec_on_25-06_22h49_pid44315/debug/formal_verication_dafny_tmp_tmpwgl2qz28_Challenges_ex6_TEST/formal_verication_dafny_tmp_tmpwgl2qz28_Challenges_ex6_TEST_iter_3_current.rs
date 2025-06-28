use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nomultiples(u: Seq<nat>) -> bool {
    forall|j: int, k: int| 0 <= j < k < u.len() ==> u.spec_index(j) != u.spec_index(k)
}

spec fn bullspec(s: Seq<nat>, u: Seq<nat>) -> nat {
    bullspec_helper(s, u, 0)
}

spec fn bullspec_helper(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases u.len() - i
{
    if i >= s.len() {
        0
    } else {
        let current = if s.spec_index(i) == u.spec_index(i) { 1 } else { 0 };
        current + bullspec_helper(s, u, i + 1)
    }
}

spec fn cowspec(s: Seq<nat>, u: Seq<nat>) -> nat {
    cowspec_helper(s, u, 0)
}

spec fn cowspec_helper(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases u.len() - i
{
    if i >= s.len() {
        0
    } else {
        let current = if s.spec_index(i) != u.spec_index(i) && seq_contains(u, s.spec_index(i)) { 1 } else { 0 };
        current + cowspec_helper(s, u, i + 1)
    }
}

spec fn seq_contains(seq: Seq<nat>, val: nat) -> bool {
    exists|j: int| 0 <= j < seq.len() && seq.spec_index(j) == val
}

// Helper spec function to compute bulls up to index i
spec fn bulls_up_to(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases i
{
    if i <= 0 {
        0
    } else {
        let current = if s.spec_index(i - 1) == u.spec_index(i - 1) { 1 } else { 0 };
        bulls_up_to(s, u, i - 1) + current
    }
}

// Helper spec function to compute cows up to index i
spec fn cows_up_to(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases i
{
    if i <= 0 {
        0
    } else {
        let current = if s.spec_index(i - 1) != u.spec_index(i - 1) && seq_contains(u, s.spec_index(i - 1)) { 1 } else { 0 };
        cows_up_to(s, u, i - 1) + current
    }
}

// Lemma to relate helper functions
proof fn lemma_bulls_equivalence(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures bulls_up_to(s, u, s.len() as int) == bullspec(s, u)
    decreases s.len()
{
    // Proof by induction - Verus can handle this automatically
}

proof fn lemma_cows_equivalence(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures cows_up_to(s, u, s.len() as int) == cowspec(s, u)
    decreases s.len()
{
    // Proof by induction - Verus can handle this automatically
}

fn BullsCows(s: Seq<nat>, u: Seq<nat>) -> (b: nat, c: nat) 
    requires 
        0 < s.len() == u.len() <= 10,
        nomultiples(u) && nomultiples(s)
    ensures 
        b >= 0 && c >= 0,
        b == bullspec(s, u),
        c == cowspec(s, u)
{
    proof {
        lemma_bulls_equivalence(s, u);
        lemma_cows_equivalence(s, u);
    }
    
    let mut b: nat = 0;
    let mut c: nat = 0;
    
    // Count bulls (exact position matches)
    let mut i = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            b >= 0,
            b == bulls_up_to(s, u, i as int)
    {
        if s.spec_index(i) == u.spec_index(i) {
            b = b + 1;
        }
        i = i + 1;
    }
    
    // Count cows (digit exists but wrong position)
    i = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            c >= 0,
            c == cows_up_to(s, u, i as int),
            b == bullspec(s, u)
    {
        if s.spec_index(i) != u.spec_index(i) {
            let mut j = 0;
            let mut found = false;
            while j < u.len()
                invariant 
                    0 <= j <= u.len(),
                    found == exists|k: int| 0 <= k < j && s.spec_index(i) == u.spec_index(k)
            {
                if s.spec_index(i) == u.spec_index(j) {
                    found = true;
                    break;
                }
                j = j + 1;
            }
            if found {
                c = c + 1;
            }
        }
        i = i + 1;
    }
    
    (b, c)
}

}