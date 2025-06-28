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
        // Base case: s has one element
        assert(s_with_x.len() == 2);
        assert(s_with_x[0] == s[0]);
        assert(s_with_x[1] == x);
        // Max(s_with_x) follows the definition for length 2
        let rest_max = Max(s_with_x.subrange(1, 2));
        assert(s_with_x.subrange(1, 2) =~= seq![x]);
        assert(rest_max == x);
        assert(Max(s_with_x) == if s[0] >= x { s[0] } else { x });
        assert(Max(s) == s[0]);
    } else {
        // Inductive case: s has more than one element
        let s_tail = s.subrange(1, s.len() as int);
        let s_with_x_tail = s_with_x.subrange(1, s_with_x.len() as int);
        
        // Key insight: s_with_x_tail == s_tail.push(x)
        assert(s_with_x_tail =~= s_tail.push(x));
        
        // Apply induction hypothesis
        lemma_max_append_one(s_tail, x);
        assert(Max(s_with_x_tail) == if x >= Max(s_tail) { x } else { Max(s_tail) });
        
        // Use definitions of Max for s and s_with_x
        let max_s_tail = Max(s_tail);
        assert(Max(s) == if s[0] >= max_s_tail { s[0] } else { max_s_tail });
        assert(Max(s_with_x) == if s[0] >= Max(s_with_x_tail) { s[0] } else { Max(s_with_x_tail) });
        
        // Now prove the postcondition by cases
        let max_s = Max(s);
        if x >= max_s {
            // Case 1: x is the new maximum
            if s[0] >= max_s_tail {
                // max_s == s[0], so x >= s[0] >= max_s_tail
                assert(Max(s_with_x_tail) == x);
                assert(Max(s_with_x) == if s[0] >= x { s[0] } else { x });
                assert(Max(s_with_x) == x);
            } else {
                // max_s == max_s_tail, so x >= max_s_tail
                assert(Max(s_with_x_tail) == x);
                assert(Max(s_with_x) == if s[0] >= x { s[0] } else { x });
                assert(Max(s_with_x) == x);
            }
        } else {
            // Case 2: x < max_s, so max should remain max_s
            if s[0] >= max_s_tail {
                // max_s == s[0] > x
                assert(Max(s_with_x_tail) == if x >= max_s_tail { x } else { max_s_tail });
                assert(Max(s_with_x) == s[0]);
                assert(Max(s_with_x) == max_s);
            } else {
                // max_s == max_s_tail > x
                assert(Max(s_with_x_tail) == max_s_tail);
                assert(Max(s_with_x) == max_s_tail);
                assert(Max(s_with_x) == max_s);
            }
        }
    }
}

proof fn lemma_min_append_one(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures Min(s.push(x)) == if x <= Min(s) { x } else { Min(s) }
    decreases s.len()
{
    let s_with_x = s.push(x);
    if s.len() == 1 {
        // Base case: s has one element
        assert(s_with_x.len() == 2);
        assert(s_with_x[0] == s[0]);
        assert(s_with_x[1] == x);
        // Min(s_with_x) follows the definition for length 2
        let rest_min = Min(s_with_x.subrange(1, 2));
        assert(s_with_x.subrange(1, 2) =~= seq![x]);
        assert(rest_min == x);
        assert(Min(s_with_x) == if s[0] <= x { s[0] } else { x });
        assert(Min(s) == s[0]);
    } else {
        // Inductive case: s has more than one element
        let s_tail = s.subrange(1, s.len() as int);
        let s_with_x_tail = s_with_x.subrange(1, s_with_x.len() as int);
        
        // Key insight: s_with_x_tail == s_tail.push(x)
        assert(s_with_x_tail =~= s_tail.push(x));
        
        // Apply induction hypothesis
        lemma_min_append_one(s_tail, x);
        assert(Min(s_with_x_tail) == if x <= Min(s_tail) { x } else { Min(s_tail) });
        
        // Use definitions of Min for s and s_with_x
        let min_s_tail = Min(s_tail);
        assert(Min(s) == if s[0] <= min_s_tail { s[0] } else { min_s_tail });
        assert(Min(s_with_x) == if s[0] <= Min(s_with_x_tail) { s[0] } else { Min(s_with_x_tail) });
        
        // Now prove the postcondition by cases
        let min_s = Min(s);
        if x <= min_s {
            // Case 1: x is the new minimum
            if s[0] <= min_s_tail {
                // min_s == s[0], so x <= s[0] <= min_s_tail
                assert(Min(s_with_x_tail) == x);
                assert(Min(s_with_x) == if s[0] <= x { s[0] } else { x });
                assert(Min(s_with_x) == x);
            } else {
                // min_s == min_s_tail, so x <= min_s_tail
                assert(Min(s_with_x_tail) == x);
                assert(Min(s_with_x) == if s[0] <= x { s[0] } else { x });
                assert(Min(s_with_x) == x);
            }
        } else {
            // Case 2: x > min_s, so min should remain min_s
            if s[0] <= min_s_tail {
                // min_s == s[0] < x
                assert(Min(s_with_x_tail) == if x <= min_s_tail { x } else { min_s_tail });
                assert(Min(s_with_x) == s[0]);
                assert(Min(s_with_x) == min_s);
            } else {
                // min_s == min_s_tail < x
                assert(Min(s_with_x_tail) == min_s_tail);
                assert(Min(s_with_x) == min_s_tail);
                assert(Min(s_with_x) == min_s);
            }
        }
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
    assert(Max(a@.subrange(0, 1)) == a[0]);
    assert(Min(a@.subrange(0, 1)) == a[0]);
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        let old_i = i;
        let current_subrange = a@.subrange(0, old_i as int);
        let next_subrange = a@.subrange(0, (old_i + 1) as int);
        
        // Prove that extending by one element
        assert(next_subrange =~= current_subrange.push(a[old_i as int]));
        
        // Apply our lemmas
        lemma_max_append_one(current_subrange, a[old_i as int]);
        lemma_min_append_one(current_subrange, a[old_i as int]);
        
        // These assertions follow from the lemmas
        assert(Max(next_subrange) == if a[old_i as int] >= max_val { a[old_i as int] } else { max_val });
        assert(Min(next_subrange) == if a[old_i as int] <= min_val { a[old_i as int] } else { min_val });
        
        // Update max and min values according to the lemma results
        if a[old_i as int] >= max_val {
            max_val = a[old_i as int];
        }
        
        if a[old_i as int] <= min_val {
            min_val = a[old_i as int];
        }
        
        i += 1;
        
        // Assert that our updates match the lemma results  
        assert(max_val == Max(a@.subrange(0, i as int)));
        assert(min_val == Min(a@.subrange(0, i as int)));
    }
    
    // Final assertion: we've processed the entire array
    assert(i == a.len());
    assert(a@.subrange(0, i as int) =~= a@);
    
    max_val - min_val
}

}