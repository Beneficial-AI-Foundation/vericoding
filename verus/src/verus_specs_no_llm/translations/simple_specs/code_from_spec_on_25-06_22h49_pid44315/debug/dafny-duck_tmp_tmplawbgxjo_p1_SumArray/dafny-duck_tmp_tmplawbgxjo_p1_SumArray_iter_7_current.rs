use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + Sum(s.subrange(0, s.len() - 1))
    }
}

// Helper lemma to prove the relationship between Sum and subranges
proof fn sum_append_lemma(s: Seq<int>, i: int)
    requires
        0 <= i < s.len()
    ensures
        Sum(s.subrange(0, i + 1)) == Sum(s.subrange(0, i)) + s[i]
    decreases i + 1
{
    let prefix = s.subrange(0, i);
    let extended = s.subrange(0, i + 1);
    
    // Key insight: extended has length i+1, so extended[extended.len()-1] = extended[i] = s[i]
    assert(extended.len() == i + 1);
    assert(extended[extended.len() - 1] == extended[i]);
    assert(extended[i] == s[i]);
    
    // By definition of Sum on extended
    assert(Sum(extended) == extended[extended.len() - 1] + Sum(extended.subrange(0, extended.len() - 1)));
    
    // extended.subrange(0, extended.len() - 1) = extended.subrange(0, i) = s.subrange(0, i)
    assert(extended.subrange(0, extended.len() - 1) == extended.subrange(0, i));
    assert(extended.subrange(0, i) == s.subrange(0, i));
    
    // Therefore Sum(extended) = s[i] + Sum(s.subrange(0, i))
    assert(Sum(extended) == s[i] + Sum(s.subrange(0, i)));
}

fn SumArray(xs: Vec<int>) -> (s: int)
    ensures
        s == Sum(xs@)
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            sum == Sum(xs@.subrange(0, i as int))
    {
        // Apply the lemma before updating
        proof {
            sum_append_lemma(xs@, i as int);
        }
        
        sum = sum + xs[i];
        i = i + 1;
    }
    
    // After the loop, i == xs.len()
    assert(i == xs.len());
    assert(xs@.subrange(0, xs.len() as int) == xs@);
    
    sum
}

}