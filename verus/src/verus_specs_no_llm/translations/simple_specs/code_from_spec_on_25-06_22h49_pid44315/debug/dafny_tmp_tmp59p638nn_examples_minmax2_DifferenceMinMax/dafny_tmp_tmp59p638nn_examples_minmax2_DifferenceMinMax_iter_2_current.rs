use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Max(s: Seq<int>) -> int
    requires s.len() > 0
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
    requires s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_min = Min(s.subrange(1, s.len() as int));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}

proof fn lemma_max_extend(s: Seq<int>, i: int)
    requires 
        s.len() > 0,
        0 < i < s.len()
    ensures
        Max(s.subrange(0, i + 1)) == if s[i] >= Max(s.subrange(0, i)) { s[i] } else { Max(s.subrange(0, i)) }
    decreases i
{
    if i == 1 {
        // Base case: s.subrange(0, 2) has 2 elements
        assert(s.subrange(0, 2) =~= seq![s[0], s[1]]);
        assert(s.subrange(0, 1) =~= seq![s[0]]);
    } else {
        // Recursive case
        lemma_max_extend(s, i - 1);
    }
}

proof fn lemma_min_extend(s: Seq<int>, i: int)
    requires 
        s.len() > 0,
        0 < i < s.len()
    ensures
        Min(s.subrange(0, i + 1)) == if s[i] <= Min(s.subrange(0, i)) { s[i] } else { Min(s.subrange(0, i)) }
    decreases i
{
    if i == 1 {
        // Base case: s.subrange(0, 2) has 2 elements
        assert(s.subrange(0, 2) =~= seq![s[0], s[1]]);
        assert(s.subrange(0, 1) =~= seq![s[0]]);
    } else {
        // Recursive case
        lemma_min_extend(s, i - 1);
    }
}

fn DifferenceMinMax(a: Vec<int>) -> (diff: int)
    requires
        a.len() > 0
    ensures
        diff == (Max(a.spec_index(..)) - Min(a.spec_index(..)))
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
        proof {
            lemma_max_extend(a@, i as int);
            lemma_min_extend(a@, i as int);
        }
        
        if a[i] > max_val {
            max_val = a[i];
        }
        if a[i] < min_val {
            min_val = a[i];
        }
        i += 1;
    }
    
    max_val - min_val
}

}