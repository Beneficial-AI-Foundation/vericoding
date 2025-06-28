use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AppendArrayToSeq(s: Seq<int>, a: Vec<int>) -> (r: Seq<int>)
    ensures
        r.len() == s.len() + a.len(),
        forall|i: int| 0 <= i < s.len() ==> r.spec_index(i) == s.spec_index(i),
        forall|i: int| 0 <= i < a.len() ==> r.spec_index(s.len() + i) == a[i]
{
    let mut result = s;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == s.len() + i,
            forall|j: int| 0 <= j < s.len() ==> result.spec_index(j) == s.spec_index(j),
            forall|j: int| 0 <= j < i ==> result.spec_index(s.len() + j) == a[j as int]
    {
        result = result.push(a[i]);
        i = i + 1;
    }
    
    result
}

}