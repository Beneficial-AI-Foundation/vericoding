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
        // Need to prove that s[0] <= Max(s) and elements in rest are <= Max(s)
        assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= Max(rest));
        assert(Max(s) == if s[0] > Max(rest) { s[0] } else { Max(rest) });
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
        // Need to prove that s[0] >= Min(s) and elements in rest are >= Min(s)
        assert(forall|i: int| 1 <= i < s.len() ==> s[i] >= Min(rest));
        assert(Min(s) == if s[0] < Min(rest) { s[0] } else { Min(rest) });
    }
}

// Lemma to show relationship between single element and pushed sequence
proof fn lemma_single_element_max(x: int)
    ensures Max(seq![x]) == x
{
}

proof fn lemma_single_element_min(x: int)  
    ensures Min(seq![x]) == x
{
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
    
    if extended.len() == 1 {
        // This case won't happen since s.len() > 0
        assert(false);
    } else {
        // extended[0] == s[0], and extended.subrange(1, extended.len()) contains s.subrange(1, s.len()) + x
        let rest = extended.subrange(1, extended.len() as int);
        
        if s.len() == 1 {
            // s = [s[0]], extended = [s[0], x], rest = [x]
            assert(rest.len() == 1);
            assert(rest[0] == x);
            lemma_single_element_max(x);
            assert(Max(rest) == x);
        } else {
            // Inductive case - more complex, but the key insight is that
            // Max(rest) will be either Max(s.subrange(1, s.len())) or x
            lemma_max_step(s.subrange(1, s.len() as int), x);
        }
    }
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
    
    if extended.len() == 1 {
        // This case won't happen since s.len() > 0
        assert(false);
    } else {
        let rest = extended.subrange(1, extended.len() as int);
        
        if s.len() == 1 {
            assert(rest.len() == 1);
            assert(rest[0] == x);
            lemma_single_element_min(x);
            assert(Min(rest) == x);
        } else {
            lemma_min_step(s.subrange(1, s.len() as int), x);
        }
    }
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
    
    // Base case: when i == 1, we have processed one element
    assert(a@.subrange(0, 1).len() == 1);
    assert(a@.subrange(0, 1)[0] == a[0]);
    lemma_single_element_max(a[0]);
    lemma_single_element_min(a[0]);
    
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
        assert(new_seq.drop_last() =~= old_seq);
        assert(new_seq.last() == a[i as int]);
        
        // We need to establish that new_seq == old_seq.push(a[i])
        assert(forall|j: int| 0 <= j < old_seq.len() ==> old_seq[j] == new_seq[j]);
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