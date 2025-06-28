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
        // Need to show that s[0] <= Max(s) and all elements in rest are <= Max(s)
        assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= Max(rest));
        assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= Max(s));
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
        // Need to show that s[0] >= Min(s) and all elements in rest are >= Min(s)
        assert(forall|i: int| 1 <= i < s.len() ==> s[i] >= Min(rest));
        assert(forall|i: int| 1 <= i < s.len() ==> s[i] >= Min(s));
    }
}

// Lemma about extending sequences for Max
proof fn lemma_max_extend(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures 
        s.push(x).len() > 0,
        Max(s.push(x)) == if x > Max(s) { x } else { Max(s) }
    decreases s.len()
{
    let extended = s.push(x);
    if s.len() == 1 {
        // Base case: s has one element
        assert(extended.len() == 2);
        assert(extended[0] == s[0]);
        assert(extended[1] == x);
        let rest_of_extended = extended.subrange(1, 2 as int);
        assert(rest_of_extended.len() == 1);
        assert(rest_of_extended[0] == x);
        assert(Max(rest_of_extended) == x);
        assert(Max(s) == s[0]);
        // The definition gives us: Max(extended) = if s[0] > x { s[0] } else { x }
    } else {
        // Inductive case
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        
        // Show that extended_rest is s_rest.push(x)
        assert(extended_rest.len() == s_rest.len() + 1);
        assert(forall|i: int| 0 <= i < s_rest.len() ==> extended_rest[i] == s_rest[i]);
        assert(extended_rest[s_rest.len() as int] == x);
        assert(extended_rest =~= s_rest.push(x));
        
        lemma_max_extend(s_rest, x);
        
        // Now we know Max(extended_rest) = if x > Max(s_rest) { x } else { Max(s_rest) }
        // And Max(s) = if s[0] > Max(s_rest) { s[0] } else { Max(s_rest) }
        // And Max(extended) = if s[0] > Max(extended_rest) { s[0] } else { Max(extended_rest) }
    }
}

// Lemma about extending sequences for Min
proof fn lemma_min_extend(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures 
        s.push(x).len() > 0,
        Min(s.push(x)) == if x < Min(s) { x } else { Min(s) }
    decreases s.len()
{
    let extended = s.push(x);
    if s.len() == 1 {
        // Base case: s has one element
        assert(extended.len() == 2);
        assert(extended[0] == s[0]);
        assert(extended[1] == x);
        let rest_of_extended = extended.subrange(1, 2 as int);
        assert(rest_of_extended.len() == 1);
        assert(rest_of_extended[0] == x);
        assert(Min(rest_of_extended) == x);
        assert(Min(s) == s[0]);
        // The definition gives us: Min(extended) = if s[0] < x { s[0] } else { x }
    } else {
        // Inductive case
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        
        // Show that extended_rest is s_rest.push(x)
        assert(extended_rest.len() == s_rest.len() + 1);
        assert(forall|i: int| 0 <= i < s_rest.len() ==> extended_rest[i] == s_rest[i]);
        assert(extended_rest[s_rest.len() as int] == x);
        assert(extended_rest =~= s_rest.push(x));
        
        lemma_min_extend(s_rest, x);
        
        // Now we know Min(extended_rest) = if x < Min(s_rest) { x } else { Min(s_rest) }
        // And Min(s) = if s[0] < Min(s_rest) { s[0] } else { Min(s_rest) }
        // And Min(extended) = if s[0] < Min(extended_rest) { s[0] } else { Min(extended_rest) }
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
    
    // Base case: when i = 1, we have processed element 0
    assert(a@.subrange(0, 1).len() == 1);
    assert(a@.subrange(0, 1)[0] == a[0]);
    assert(Max(a@.subrange(0, 1)) == a[0]);
    assert(Min(a@.subrange(0, 1)) == a[0]);
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            a@.subrange(0, i as int).len() > 0,
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        let current_seq = a@.subrange(0, i as int);
        let next_seq = a@.subrange(0, (i + 1) as int);
        
        // Establish that next_seq is current_seq.push(a[i])
        assert(next_seq.len() == current_seq.len() + 1);
        assert(forall|j: int| 0 <= j < current_seq.len() ==> next_seq[j] == current_seq[j]);
        assert(next_seq[current_seq.len() as int] == a[i as int]);
        assert(next_seq =~= current_seq.push(a[i as int]));
        
        // Apply our lemmas
        proof {
            lemma_max_extend(current_seq, a[i as int]);
            lemma_min_extend(current_seq, a[i as int]);
        }
        
        // Update values based on the lemmas
        if a[i] > max_val {
            max_val = a[i];
        }
        
        if a[i] < min_val {
            min_val = a[i];
        }
        
        // The lemmas tell us what the new max and min should be
        assert(max_val == (if a[i as int] > Max(current_seq) { a[i as int] } else { Max(current_seq) }));
        assert(min_val == (if a[i as int] < Min(current_seq) { a[i as int] } else { Min(current_seq) }));
        assert(max_val == Max(next_seq));
        assert(min_val == Min(next_seq));
        
        i += 1;
    }
    
    // At loop exit, we have processed all elements
    assert(i == a.len());
    assert(a@.subrange(0, a.len() as int) =~= a@);
    assert(max_val == Max(a@));
    assert(min_val == Min(a@));
    
    max_val + min_val
}

}