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
        // Max(extended) will compare extended[0] with Max(extended.subrange(1,2))
        // extended.subrange(1,2) has length 1 and contains only x
        assert(extended.subrange(1, 2 as int).len() == 1);
        assert(extended.subrange(1, 2 as int)[0] == x);
        assert(Max(extended.subrange(1, 2 as int)) == x);
    } else {
        // Inductive case
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        
        // Show that extended_rest equals s_rest.push(x)
        assert(extended_rest.len() == s_rest.len() + 1);
        assert(forall|i: int| 0 <= i < s_rest.len() ==> extended_rest[i] == s_rest[i]);
        assert(extended_rest[s_rest.len() as int] == x);
        assert(extended_rest == s_rest.push(x));
        
        lemma_max_extend(s_rest, x);
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
        assert(extended.subrange(1, 2 as int).len() == 1);
        assert(extended.subrange(1, 2 as int)[0] == x);
        assert(Min(extended.subrange(1, 2 as int)) == x);
    } else {
        // Inductive case
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        
        assert(extended_rest.len() == s_rest.len() + 1);
        assert(forall|i: int| 0 <= i < s_rest.len() ==> extended_rest[i] == s_rest[i]);
        assert(extended_rest[s_rest.len() as int] == x);
        assert(extended_rest == s_rest.push(x));
        
        lemma_min_extend(s_rest, x);
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
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        let current_seq = a@.subrange(0, i as int);
        let next_seq = a@.subrange(0, (i + 1) as int);
        
        // Establish relationship between current_seq and next_seq
        assert(next_seq.len() == current_seq.len() + 1);
        assert(forall|j: int| 0 <= j < current_seq.len() ==> next_seq[j] == current_seq[j]);
        assert(next_seq[current_seq.len() as int] == a[i as int]);
        assert(next_seq == current_seq.push(a[i as int]));
        
        // Apply our lemmas
        proof {
            lemma_max_extend(current_seq, a[i as int]);
            lemma_min_extend(current_seq, a[i as int]);
        }
        
        // Update max_val
        if a[i] > max_val {
            max_val = a[i];
        }
        
        // Update min_val  
        if a[i] < min_val {
            min_val = a[i];
        }
        
        i += 1;
    }
    
    // At loop exit, i == a.len()
    assert(i == a.len());
    assert(a@.subrange(0, i as int) == a@.subrange(0, a.len() as int));
    assert(a@.subrange(0, a.len() as int) == a@);
    
    max_val + min_val
}

}