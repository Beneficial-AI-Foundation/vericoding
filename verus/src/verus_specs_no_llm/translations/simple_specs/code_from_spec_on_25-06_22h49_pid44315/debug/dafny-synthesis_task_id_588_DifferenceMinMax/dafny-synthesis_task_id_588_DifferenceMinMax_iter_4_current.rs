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
        assert(s_with_x[0] == s[0]);
        assert(s_with_x[1] == x);
        assert(Max(s_with_x) == if s[0] >= x { s[0] } else { x });
        assert(Max(s) == s[0]);
        assert(Max(s_with_x) == if x >= Max(s) { x } else { Max(s) });
    } else {
        // s.len() > 1, so s_with_x.len() > 2
        let s_tail = s.subrange(1, s.len() as int);
        let s_with_x_tail = s_with_x.subrange(1, s_with_x.len() as int);
        
        // Show that s_with_x_tail == s_tail.push(x)
        assert(s_with_x_tail =~= s_tail.push(x));
        
        // Apply induction hypothesis
        lemma_max_append_one(s_tail, x);
        
        // Now we can reason about Max(s_with_x)
        let max_s_tail = Max(s_tail);
        let max_s_with_x_tail = Max(s_with_x_tail);
        
        assert(max_s_with_x_tail == if x >= max_s_tail { x } else { max_s_tail });
        
        let max_s = Max(s);
        let max_s_with_x = Max(s_with_x);
        
        assert(max_s == if s[0] >= max_s_tail { s[0] } else { max_s_tail });
        assert(max_s_with_x == if s[0] >= max_s_with_x_tail { s[0] } else { max_s_with_x_tail });
        
        // Case analysis to prove the postcondition
        if x >= max_s {
            if s[0] >= max_s_tail {
                // max_s == s[0], and x >= s[0]
                assert(max_s_with_x_tail == if x >= max_s_tail { x } else { max_s_tail });
                assert(x >= max_s_tail); // since x >= max_s == s[0] >= max_s_tail
                assert(max_s_with_x_tail == x);
                assert(max_s_with_x == if s[0] >= x { s[0] } else { x });
                assert(max_s_with_x == x); // since x >= max_s == s[0]
            } else {
                // max_s == max_s_tail, and x >= max_s_tail
                assert(max_s_with_x_tail == x);
                assert(max_s_with_x == if s[0] >= x { s[0] } else { x });
                assert(max_s_with_x == x); // since x >= max_s >= s[0]
            }
        } else {
            // x < max_s
            if s[0] >= max_s_tail {
                // max_s == s[0] > x
                if x >= max_s_tail {
                    assert(max_s_with_x_tail == x);
                    assert(max_s_with_x == s[0]); // since s[0] > x
                } else {
                    assert(max_s_with_x_tail == max_s_tail);
                    assert(max_s_with_x == s[0]); // since s[0] >= max_s_tail
                }
                assert(max_s_with_x == s[0]);
                assert(max_s_with_x == max_s);
            } else {
                // max_s == max_s_tail > x
                assert(max_s_with_x_tail == max_s_tail);
                assert(max_s_with_x == max_s_tail);
                assert(max_s_with_x == max_s);
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
        // s = [s[0]], s_with_x = [s[0], x]
        assert(s_with_x.len() == 2);
        assert(s_with_x[0] == s[0]);
        assert(s_with_x[1] == x);
        assert(Min(s_with_x) == if s[0] <= x { s[0] } else { x });
        assert(Min(s) == s[0]);
        assert(Min(s_with_x) == if x <= Min(s) { x } else { Min(s) });
    } else {
        // s.len() > 1, so s_with_x.len() > 2
        let s_tail = s.subrange(1, s.len() as int);
        let s_with_x_tail = s_with_x.subrange(1, s_with_x.len() as int);
        
        // Show that s_with_x_tail == s_tail.push(x)
        assert(s_with_x_tail =~= s_tail.push(x));
        
        // Apply induction hypothesis
        lemma_min_append_one(s_tail, x);
        
        // Now we can reason about Min(s_with_x)
        let min_s_tail = Min(s_tail);
        let min_s_with_x_tail = Min(s_with_x_tail);
        
        assert(min_s_with_x_tail == if x <= min_s_tail { x } else { min_s_tail });
        
        let min_s = Min(s);
        let min_s_with_x = Min(s_with_x);
        
        assert(min_s == if s[0] <= min_s_tail { s[0] } else { min_s_tail });
        assert(min_s_with_x == if s[0] <= min_s_with_x_tail { s[0] } else { min_s_with_x_tail });
        
        // Case analysis to prove the postcondition
        if x <= min_s {
            if s[0] <= min_s_tail {
                // min_s == s[0], and x <= s[0]
                assert(min_s_with_x_tail == if x <= min_s_tail { x } else { min_s_tail });
                assert(x <= min_s_tail); // since x <= min_s == s[0] <= min_s_tail
                assert(min_s_with_x_tail == x);
                assert(min_s_with_x == if s[0] <= x { s[0] } else { x });
                assert(min_s_with_x == x); // since x <= min_s == s[0]
            } else {
                // min_s == min_s_tail, and x <= min_s_tail
                assert(min_s_with_x_tail == x);
                assert(min_s_with_x == if s[0] <= x { s[0] } else { x });
                assert(min_s_with_x == x); // since x <= min_s <= s[0]
            }
        } else {
            // x > min_s
            if s[0] <= min_s_tail {
                // min_s == s[0] < x
                if x <= min_s_tail {
                    assert(min_s_with_x_tail == x);
                    assert(min_s_with_x == s[0]); // since s[0] < x
                } else {
                    assert(min_s_with_x_tail == min_s_tail);
                    assert(min_s_with_x == s[0]); // since s[0] <= min_s_tail
                }
                assert(min_s_with_x == s[0]);
                assert(min_s_with_x == min_s);
            } else {
                // min_s == min_s_tail < x
                assert(min_s_with_x_tail == min_s_tail);
                assert(min_s_with_x == min_s_tail);
                assert(min_s_with_x == min_s);
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
        let current_subrange = a@.subrange(0, i as int);
        let next_subrange = a@.subrange(0, (i + 1) as int);
        
        // Prove that extending by one element
        assert(next_subrange =~= current_subrange.push(a[i as int]));
        
        // Apply our lemmas
        lemma_max_append_one(current_subrange, a[i as int]);
        lemma_min_append_one(current_subrange, a[i as int]);
        
        // Update max and min values according to the lemma results
        if a[i] >= max_val {
            max_val = a[i];
        } else {
            // max_val remains the same
        }
        
        if a[i] <= min_val {
            min_val = a[i];
        } else {
            // min_val remains the same
        }
        
        // Assert that our updates match the lemma results
        assert(max_val == Max(next_subrange));
        assert(min_val == Min(next_subrange));
        
        i += 1;
    }
    
    // Final assertion: we've processed the entire array
    assert(i == a.len());
    assert(a@.subrange(0, i as int) =~= a@);
    
    max_val - min_val
}

}