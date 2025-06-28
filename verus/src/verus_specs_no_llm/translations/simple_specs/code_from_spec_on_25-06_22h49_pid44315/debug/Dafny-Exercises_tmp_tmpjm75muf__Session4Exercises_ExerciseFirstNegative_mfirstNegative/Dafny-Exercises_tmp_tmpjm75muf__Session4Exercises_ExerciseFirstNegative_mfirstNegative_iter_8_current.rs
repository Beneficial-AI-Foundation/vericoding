use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int| 0 <= u < s.len() ==> s[u] >= 0
}

fn firstNegative(v: Vec<int>) -> (b: bool, i: int)
    ensures
        b <==> exists |k: int| 0 <= k < v.len() && v@[k] < 0,
        b ==> 0 <= i < v.len() && v@[i] < 0 && positive(v@.subrange(0, i))
{
    let mut index: usize = 0;
    
    while index < v.len()
        invariant
            0 <= index <= v.len(),
            positive(v@.subrange(0, index as int)),
    {
        if v[index] < 0 {
            return (true, index as int);
        }
        index += 1;
    }
    
    (false, 0)
}

}