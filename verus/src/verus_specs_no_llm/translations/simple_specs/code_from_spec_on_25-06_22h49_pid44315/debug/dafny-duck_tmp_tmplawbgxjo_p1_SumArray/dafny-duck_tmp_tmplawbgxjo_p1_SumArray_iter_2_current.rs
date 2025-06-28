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
        sum = sum + xs[i];
        i = i + 1;
    }
    
    sum
}

}