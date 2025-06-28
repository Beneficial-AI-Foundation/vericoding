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

// Helper lemmas to prove properties about Max and Min when appending elements
proof fn lemma_max_append_one(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures Max(s.push(x)) == if x >= Max(s) { x } else { Max(s) }
    decreases s.len()
{
    let s_with_x = s.push(x);
    if s.len() == 1 {
        // s = [s[0]], s_with_x = [s[0], x]
        assert(s_with_x.len() == 2);
        assert(Max(s_with_x) == if s[0] >= x { s[0] } else { x });
        assert(Max(s) == s[0]);
    } else {
        // s.len() > 1, so s_with_x.len() > 2
        let s_tail = s.subrange(1, s.len() as int);
        let s_with_x_tail = s_with_x.subrange(1, s_with_x.len() as int);
        
        // Show that s_with_x_tail == s_tail.push(x)
        assert(s_with_x_tail =~= s_tail.push(x));
        
        // Apply induction hypothesis
        lemma_max_append_one(s_tail, x);
        
        // Now we can reason about Max(s_with_x)
        assert(Max(s_with_x) == if s[0] >= Max(s_with_x_tail) { s[0] } else { Max(s_with_x_tail) });
        assert(Max(s) == if s[0] >= Max(s_tail) { s[0] } else { Max(s_tail) });
    }
}

proof fn lemma_min_append_one(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures Min(s.push(x)) == if x <= Min(s) { x } else { Min(s) }
    decreases s.len()
{
    let s_with_x = s.push(x);
    if s.len() == 1 {
        // s = [s[0]], s_with_x = [s[0], x]
        assert(s_with_x.len() == 2);
        assert(Min(s_with_x) == if s[0] <= x { s[0] } else { x });
        assert(Min(s) == s[0]);
    } else {
        // s.len() > 1, so s_with_x.len() > 2
        let s_tail = s.subrange(1, s.len() as int);
        let s_with_x_tail = s_with_x.subrange(1, s_with_x.len() as int);
        
        // Show that s_with_x_tail == s_tail.push(x)
        assert(s_with_x_tail =~= s_tail.push(x));
        
        // Apply induction hypothesis
        lemma_min_append_one(s_tail, x);
        
        // Now we can reason about Min(s_with_x)
        assert(Min(s_with_x) == if s[0] <= Min(s_with_x_tail) { s[0] } else { Min(s_with_x_tail) });
        assert(Min(s) == if s[0] <= Min(s_tail) { s[0] } else { Min(s_tail) });
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
    
    // Establish base case
    assert(a@.subrange(0, 1) =~= seq![a[0]]);
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        let current_subrange = a@.subrange(0, i as int);
        let next_subrange = a@.subrange(0, (i + 1) as int);
        
        // Prove that extending by one element
        assert(next_subrange =~= current_subrange.push(a[i as int]));
        
        // Apply our lemmas
        lemma_max_append_one(current_subrange, a[i as int]);
        lemma_min_append_one(current_subrange, a[i as int]);
        
        // Update max and min values
        if a[i] > max_val {
            max_val = a[i];
        }
        if a[i] < min_val {
            min_val = a[i];
        }
        
        i += 1;
    }
    
    // Final assertion: we've processed the entire array
    assert(a@.subrange(0, i as int) =~= a@);
    
    max_val - min_val
}

}

The key changes I made:


The verification should now succeed because:
- The lemmas correctly prove the relationship between `Max`/`Min` of a sequence and the same sequence with one element appended
- The main function properly maintains the invariants using these lemmas
- All sequence manipulations are properly proven with equality assertions