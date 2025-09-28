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
    let mut result = s;
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == s.len() + i,
            forall|j: int| 0 <= j < s.len() ==> result[j] == s[j],
            forall|j: int| 0 <= j < i ==> result[s.len() + j] == a[j],
    {
        result = result.add(seq![a[i]]);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}

}