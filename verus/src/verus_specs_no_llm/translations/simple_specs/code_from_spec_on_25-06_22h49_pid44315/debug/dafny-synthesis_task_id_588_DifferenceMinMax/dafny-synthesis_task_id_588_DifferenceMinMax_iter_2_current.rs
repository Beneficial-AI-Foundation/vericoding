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
        if s[0] >= rest_max { s[0] } else { rest_max }
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
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}

// Helper lemmas to prove properties about Max and Min
proof fn lemma_max_extend(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures Max(s.push(x)) == if x >= Max(s) { x } else { Max(s) }
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: s has one element
        assert(s.push(x).len() == 2);
        assert(s.push(x)[0] == s[0]);
        assert(s.push(x)[1] == x);
        assert(Max(s.push(x)) == if s[0] >= x { s[0] } else { x });
        assert(Max(s) == s[0]);
    } else {
        // Recursive case
        let s_tail = s.subrange(1, s.len() as int);
        let s_new = s.push(x);
        let s_new_tail = s_new.subrange(1, s_new.len() as int);
        
        assert(s_new_tail == s_tail.push(x));
        lemma_max_extend(s_tail, x);
    }
}

proof fn lemma_min_extend(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures Min(s.push(x)) == if x <= Min(s) { x } else { Min(s) }
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: s has one element
        assert(s.push(x).len() == 2);
        assert(s.push(x)[0] == s[0]);
        assert(s.push(x)[1] == x);
        assert(Min(s.push(x)) == if s[0] <= x { s[0] } else { x });
        assert(Min(s) == s[0]);
    } else {
        // Recursive case
        let s_tail = s.subrange(1, s.len() as int);
        let s_new = s.push(x);
        let s_new_tail = s_new.subrange(1, s_new.len() as int);
        
        assert(s_new_tail == s_tail.push(x));
        lemma_min_extend(s_tail, x);
    }
}

fn DifferenceMinMax(a: Vec<int>) -> (diff: int)
    requires
        a.len() > 0
    ensures
        diff == Max(a@) - Min(a@)
{
    let mut max_val = a[0];
    let mut min_val = a[0];
    let mut i = 1;
    
    // Base case: first element
    assert(a@.subrange(0, 1) == seq![a[0]]);
    assert(Max(a@.subrange(0, 1)) == a[0]);
    assert(Min(a@.subrange(0, 1)) == a[0]);
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        let old_max = max_val;
        let old_min = min_val;
        let current_seq = a@.subrange(0, i as int);
        let next_seq = a@.subrange(0, (i + 1) as int);
        
        // Prove that next_seq is current_seq with a[i] appended
        assert(next_seq == current_seq.push(a[i as int]));
        
        // Apply lemmas
        lemma_max_extend(current_seq, a[i as int]);
        lemma_min_extend(current_seq, a[i as int]);
        
        if a[i] > max_val {
            max_val = a[i];
        }
        if a[i] < min_val {
            min_val = a[i];
        }
        
        // Verify the invariant holds
        assert(max_val == Max(next_seq));
        assert(min_val == Min(next_seq));
        
        i += 1;
    }
    
    // At the end, we have processed the entire array
    assert(i == a.len());
    assert(a@.subrange(0, i as int) == a@);
    
    max_val - min_val
}

}