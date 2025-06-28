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

// Simplified helper lemmas
proof fn lemma_max_append_one(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures Max(s.push(x)) == if x >= Max(s) { x } else { Max(s) }
    decreases s.len()
{
    let s_with_x = s.push(x);
    if s.len() == 1 {
        assert(s_with_x =~= seq![s[0], x]);
        assert(Max(s) == s[0]);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        lemma_max_append_one(s_tail, x);
    }
}

proof fn lemma_min_append_one(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures Min(s.push(x)) == if x <= Min(s) { x } else { Min(s) }
    decreases s.len()
{
    let s_with_x = s.push(x);
    if s.len() == 1 {
        assert(s_with_x =~= seq![s[0], x]);
        assert(Min(s) == s[0]);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        lemma_min_append_one(s_tail, x);
    }
}

// Additional helper lemma for subrange extension
proof fn lemma_subrange_extend(s: Seq<int>, i: int)
    requires 0 < i < s.len()
    ensures s.subrange(0, i + 1) == s.subrange(0, i).push(s[i])
{
    let shorter = s.subrange(0, i);
    let longer = s.subrange(0, i + 1);
    assert(longer.len() == shorter.len() + 1);
    assert forall |j| 0 <= j < shorter.len() implies longer[j] == shorter[j];
    assert(longer[i] == s[i]);
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
    
    // Base case proof
    assert(a@.subrange(0, 1) =~= seq![a[0]]);
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        let old_i = i;
        let current_range = a@.subrange(0, old_i as int);
        let next_range = a@.subrange(0, (old_i + 1) as int);
        
        // Prove the subrange relationship
        lemma_subrange_extend(a@, old_i as int);
        assert(next_range == current_range.push(a[old_i]));
        
        // Apply the helper lemmas
        lemma_max_append_one(current_range, a[old_i]);
        lemma_min_append_one(current_range, a[old_i]);
        
        // Update values based on comparisons
        if a[old_i] > max_val {
            max_val = a[old_i];
        }
        
        if a[old_i] < min_val {
            min_val = a[old_i];
        }
        
        i += 1;
    }
    
    // Final assertions
    assert(i == a.len());
    assert(a@.subrange(0, a.len() as int) =~= a@);
    
    max_val - min_val
}

}