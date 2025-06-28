use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires
        s1.len() == s2.len() && s2.len() == s3.len()
    ensures
        r.len() == 3 * s1.len(),
        forall|i: int| 0 <= i < s1.len() ==> r.spec_index(3*i) == s1.spec_index(i) && r.spec_index(3*i + 1) == s2.spec_index(i) && r.spec_index(3*i + 2) == s3.spec_index(i)
{
    let mut result = Seq::<int>::empty();
    let mut idx = 0;
    
    while idx < s1.len()
        invariant
            s1.len() == s2.len() && s2.len() == s3.len(),
            0 <= idx <= s1.len(),
            result.len() == 3 * idx,
            forall|i: int| 0 <= i < idx ==> result.spec_index(3*i) == s1.spec_index(i) && result.spec_index(3*i + 1) == s2.spec_index(i) && result.spec_index(3*i + 2) == s3.spec_index(i)
    {
        result = result.push(s1.spec_index(idx));
        result = result.push(s2.spec_index(idx));
        result = result.push(s3.spec_index(idx));
        idx = idx + 1;
    }
    
    result
}

}