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

// Helper lemmas to establish properties about Max and Min
proof fn lemma_max_extend(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures Max(s.push(x)) == if x > Max(s) { x } else { Max(s) }
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: s has one element
        let extended = s.push(x);
        assert(extended.len() == 2);
        assert(extended[0] == s[0]);
        assert(extended[1] == x);
        assert(Max(extended) == if extended[0] > extended[1] { extended[0] } else { extended[1] });
    } else {
        // Inductive case
        let extended = s.push(x);
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        assert(extended_rest == s_rest.push(x));
        lemma_max_extend(s_rest, x);
    }
}

proof fn lemma_min_extend(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures Min(s.push(x)) == if x < Min(s) { x } else { Min(s) }
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: s has one element
        let extended = s.push(x);
        assert(extended.len() == 2);
        assert(extended[0] == s[0]);
        assert(extended[1] == x);
        assert(Min(extended) == if extended[0] < extended[1] { extended[0] } else { extended[1] });
    } else {
        // Inductive case
        let extended = s.push(x);
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        assert(extended_rest == s_rest.push(x));
        lemma_min_extend(s_rest, x);
    }
}

fn SumMinMax(a: Vec<int>) -> (sum: int)
    requires
        a.len() > 0
    ensures
        sum == Max(a.spec_index(..)) + Min(a.spec_index(..))
{
    let mut max_val = a[0];
    let mut min_val = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max_val == Max(a.spec_index(..i as int)),
            min_val == Min(a.spec_index(..i as int))
    {
        let old_i = i;
        let current_seq = a.spec_index(..i as int);
        let next_seq = a.spec_index(..(i + 1) as int);
        
        // Prove that next_seq is current_seq.push(a[i])
        assert(next_seq == current_seq.push(a[i as int]));
        
        // Apply lemmas
        proof {
            lemma_max_extend(current_seq, a[i as int]);
            lemma_min_extend(current_seq, a[i as int]);
        }
        
        if a[i] > max_val {
            max_val = a[i];
        }
        if a[i] < min_val {
            min_val = a[i];
        }
        i += 1;
        
        // Assert the invariant holds
        assert(max_val == Max(a.spec_index(..i as int)));
        assert(min_val == Min(a.spec_index(..i as int)));
    }
    
    // At the end, i == a.len(), so we have the max and min of the entire array
    assert(i == a.len());
    assert(a.spec_index(..i as int) == a.spec_index(..));
    
    max_val + min_val
}

}