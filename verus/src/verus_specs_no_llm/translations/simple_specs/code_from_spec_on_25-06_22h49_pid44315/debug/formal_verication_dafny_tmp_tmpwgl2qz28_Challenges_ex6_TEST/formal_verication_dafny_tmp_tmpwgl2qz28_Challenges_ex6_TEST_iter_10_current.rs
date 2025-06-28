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
    decreases s.len() - i
{
    if i >= s.len() || i >= u.len() {
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
    decreases s.len() - i
{
    if i >= s.len() || i >= u.len() {
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
    } else if i > s.len() || i > u.len() {
        let min_len = if s.len() <= u.len() { s.len() } else { u.len() };
        bulls_up_to(s, u, min_len)
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
    } else if i > s.len() || i > u.len() {
        let min_len = if s.len() <= u.len() { s.len() } else { u.len() };
        cows_up_to(s, u, min_len)
    } else {
        let current = if s.spec_index(i - 1) != u.spec_index(i - 1) && seq_contains(u, s.spec_index(i - 1)) { 1 } else { 0 };
        cows_up_to(s, u, i - 1) + current
    }
}

// Lemma to prove that seq_contains can be checked by iteration
proof fn lemma_seq_contains_found(seq: Seq<nat>, val: nat, j: int)
    requires 
        0 <= j < seq.len(),
        seq.spec_index(j) == val
    ensures seq_contains(seq, val)
{
}

// Lemma to relate helper functions
proof fn lemma_bulls_equivalence(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures bulls_up_to(s, u, s.len()) == bullspec(s, u)
{
    if s.len() > 0 {
        lemma_bulls_helper(s, u, 0, s.len());
    }
}

proof fn lemma_bulls_helper(s: Seq<nat>, u: Seq<nat>, i: int, len: int)
    requires 
        s.len() == u.len(),
        s.len() == len,
        0 <= i <= len
    ensures 
        bulls_up_to(s, u, len) == bulls_up_to(s, u, i) + bullspec_helper(s, u, i)
    decreases len - i
{
    if i < len {
        lemma_bulls_helper(s, u, i + 1, len);
    }
}

proof fn lemma_cows_equivalence(s: Seq<nat>, u: Seq<nat>)
    requires s.len() == u.len()
    ensures cows_up_to(s, u, s.len()) == cowspec(s, u)
{
    if s.len() > 0 {
        lemma_cows_helper(s, u, 0, s.len());
    }
}

proof fn lemma_cows_helper(s: Seq<nat>, u: Seq<nat>, i: int, len: int)
    requires 
        s.len() == u.len(),
        s.len() == len,
        0 <= i <= len
    ensures 
        cows_up_to(s, u, len) == cows_up_to(s, u, i) + cowspec_helper(s, u, i)
    decreases len - i
{
    if i < len {
        lemma_cows_helper(s, u, i + 1, len);
    }
}

proof fn lemma_seq_contains_not_found(seq: Seq<nat>, val: nat)
    requires forall|k: int| 0 <= k < seq.len() ==> val != seq.spec_index(k)
    ensures !seq_contains(seq, val)
{
}

proof fn lemma_bulls_step(s: Seq<nat>, u: Seq<nat>, i: int)
    requires 
        s.len() == u.len(),
        0 <= i < s.len()
    ensures 
        bulls_up_to(s, u, i + 1) == bulls_up_to(s, u, i) + (if s.spec_index(i) == u.spec_index(i) { 1 } else { 0 })
{
}

proof fn lemma_cows_step(s: Seq<nat>, u: Seq<nat>, i: int)
    requires 
        s.len() == u.len(),
        0 <= i < s.len()
    ensures 
        cows_up_to(s, u, i + 1) == cows_up_to(s, u, i) + (if s.spec_index(i) != u.spec_index(i) && seq_contains(u, s.spec_index(i)) { 1 } else { 0 })
{
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
    let mut i: usize = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            s.len() == u.len(),
            b == bulls_up_to(s, u, i as int)
    {
        if s.spec_index(i as int) == u.spec_index(i as int) {
            b = b + 1;
        }
        
        proof {
            lemma_bulls_step(s, u, i as int);
        }
        
        i = i + 1;
    }
    
    // Count cows (digit exists but wrong position)
    i = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            s.len() == u.len(),
            c == cows_up_to(s, u, i as int),
            b == bullspec(s, u)
    {
        if s.spec_index(i as int) != u.spec_index(i as int) {
            // Check if s[i] exists anywhere in u
            let mut j: usize = 0;
            let mut found = false;
            while j < u.len()
                invariant 
                    0 <= j <= u.len(),
                    found ==> seq_contains(u, s.spec_index(i as int)),
                    !found ==> forall|k: int| 0 <= k < j ==> s.spec_index(i as int) != u.spec_index(k)
            {
                if s.spec_index(i as int) == u.spec_index(j as int) {
                    found = true;
                    proof {
                        lemma_seq_contains_found(u, s.spec_index(i as int), j as int);
                    }
                    break;
                }
                j = j + 1;
            }
            
            proof {
                if !found {
                    lemma_seq_contains_not_found(u, s.spec_index(i as int));
                }
            }
            
            if found {
                c = c + 1;
            }
        }
        
        proof {
            lemma_cows_step(s, u, i as int);
        }
        
        i = i + 1;
    }
    
    (b, c)
}

}