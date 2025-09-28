use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn insert_before_each(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures
        v.len() == 2 * s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[2*i] == x && v[2*i + 1] == s[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Seq::<String>::empty();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == 2 * i,
            forall|j: int| 0 <= j < i ==> result[2*j] == x && result[2*j + 1] == s[j],
    {
        result = result.push(x.clone());
        result = result.push(s[i as int].clone());
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}