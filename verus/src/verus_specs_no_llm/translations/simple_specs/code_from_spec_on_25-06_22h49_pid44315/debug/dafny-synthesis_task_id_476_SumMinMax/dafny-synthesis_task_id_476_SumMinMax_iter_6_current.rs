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
        assert(extended.subrange(1, 2 as int).len() == 1);
        assert(extended.subrange(1, 2 as int)[0] == x);
        assert(Max(extended.subrange(1, 2 as int)) == x);
        assert(Max(s) == s[0]);
    } else {
        // Inductive case
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        
        assert(extended_rest =~= s_rest.push(x));
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
        assert(Min(s) == s[0]);
    } else {
        // Inductive case
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        
        assert(extended_rest =~= s_rest.push(x));
        lemma_min_extend(s_rest, x);
    }
}

// Helper lemma to relate prefix sequences
proof fn lemma_prefix_relationship(s: Seq<int>, i: int, j: int)
    requires 0 <= i < j <= s.len()
    ensures 
        s.subrange(0, j).subrange(0, i) =~= s.subrange(0, i),
        s.subrange(0, j)[i] == s[i]
{
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
        
        // Assert the postcondition for next iteration
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