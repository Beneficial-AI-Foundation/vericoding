use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn append_array_to_seq(s: Seq<i32>, a: &Vec<i32>) -> (r: Seq<i32>)
    ensures
        r.len() == s.len() + a.len(),
        forall|i: int| 0 <= i < s.len() ==> r[i] == s[i],
        forall|i: int| 0 <= i < a.len() ==> r[s.len() + i] == a[i],
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    // First, add all elements from the original sequence
    while i < s.len() as usize
        invariant
            i as int <= s.len(),
            v@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> v@[j] == s[j],
    {
        v.push(s[i as int]);
        i = i + 1;
    }
    
    // Then, add all elements from the array
    i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            v@.len() == s.len() + i as int,
            forall|j: int| 0 <= j < s.len() ==> v@[j] == s[j],
            forall|j: int| 0 <= j < i as int ==> v@[s.len() + j] == a@[j],
    {
        v.push(a[i]);
        i = i + 1;
    }
    
    v@
}
// </vc-code>

fn main() {}

}