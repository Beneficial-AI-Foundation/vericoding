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
    
    if i == 0 {
        assert(extended.len() == 1);
        assert(extended[0] == s[0]);
        assert(Sum(extended) == s[0] + Sum(extended.subrange(0, 0)));
        assert(extended.subrange(0, 0).len() == 0);
        assert(Sum(extended.subrange(0, 0)) == 0);
        assert(Sum(extended) == s[0]);
        assert(prefix.len() == 0);
        assert(Sum(prefix) == 0);
    } else {
        assert(extended.len() == i + 1);
        assert(extended[extended.len() - 1] == s[i]);
        assert(Sum(extended) == extended[extended.len() - 1] + Sum(extended.subrange(0, extended.len() - 1)));
        assert(extended.subrange(0, extended.len() - 1) == s.subrange(0, i));
        assert(Sum(extended) == s[i] + Sum(s.subrange(0, i)));
    }
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
        proof {
            sum_append_lemma(xs@, i as int);
        }
        sum = sum + xs[i];
        i = i + 1;
    }
    
    assert(i == xs.len());
    assert(xs@.subrange(0, xs.len() as int) == xs@);
    
    sum
}

}