use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Max(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_max = Max(s.subrange(1, s.len() as int));
        if s[0] > rest_max { s[0] } else { rest_max }
    }
}

spec fn Min(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_min = Min(s.subrange(1, s.len() as int));
        if s[0] < rest_min { s[0] } else { rest_min }
    }
}

// Helper lemma for Max properties
proof fn lemma_max_properties(s: Seq<int>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> s[i] <= Max(s)
    decreases s.len()
{
    if s.len() == 1 {
        // Base case is trivial
    } else {
        let rest = s.subrange(1, s.len() as int);
        lemma_max_properties(rest);
    }
}

// Helper lemma for Min properties  
proof fn lemma_min_properties(s: Seq<int>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> s[i] >= Min(s)
    decreases s.len()
{
    if s.len() == 1 {
        // Base case is trivial
    } else {
        let rest = s.subrange(1, s.len() as int);
        lemma_min_properties(rest);
    }
}

// Simplified lemma for Max when extending by one element
proof fn lemma_max_step(s: Seq<int>, x: int)
    requires 
        s.len() > 0
    ensures 
        s.push(x).len() > 0,
        Max(s.push(x)) == if x > Max(s) { x } else { Max(s) }
{
    let extended = s.push(x);
    assert(extended.len() == s.len() + 1);
    assert(extended.last() == x);
    
    // The proof follows from the recursive definition
    let rest = extended.subrange(1, extended.len() as int);
    assert(rest =~= s.subrange(1, s.len() as int).push(x));
}

// Simplified lemma for Min when extending by one element  
proof fn lemma_min_step(s: Seq<int>, x: int)
    requires 
        s.len() > 0
    ensures 
        s.push(x).len() > 0,
        Min(s.push(x)) == if x < Min(s) { x } else { Min(s) }
{
    let extended = s.push(x);
    assert(extended.len() == s.len() + 1);
    assert(extended.last() == x);
    
    // The proof follows from the recursive definition
    let rest = extended.subrange(1, extended.len() as int);
    assert(rest =~= s.subrange(1, s.len() as int).push(x));
}

fn SumMinMax(a: Vec<int>) -> (sum: int)
    requires
        a.len() > 0
    ensures
        sum == Max(a@) + Min(a@)
{
    let mut max_val = a[0];
    let mut min_val = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            a@.subrange(0, i as int).len() > 0,
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        let old_seq = a@.subrange(0, i as int);
        let new_seq = a@.subrange(0, (i + 1) as int);
        
        // Show the relationship between old and new sequences
        assert(new_seq.len() == old_seq.len() + 1);
        assert(new_seq =~= old_seq.push(a[i as int]));
        
        // Apply the step lemmas
        proof {
            lemma_max_step(old_seq, a[i as int]);
            lemma_min_step(old_seq, a[i as int]);
        }
        
        // Update max
        if a[i] > max_val {
            max_val = a[i];
        }
        
        // Update min
        if a[i] < min_val {
            min_val = a[i];
        }
        
        i += 1;
    }
    
    // Final assertion
    assert(a@.subrange(0, a.len() as int) =~= a@);
    
    max_val + min_val
}

}