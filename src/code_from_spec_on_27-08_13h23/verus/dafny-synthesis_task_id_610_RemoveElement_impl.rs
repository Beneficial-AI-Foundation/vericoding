use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove properties about sequence indexing and shifting
proof fn lemma_vec_remove_element(s: &Vec<i32>, k: usize)
    requires 
        k < s.len(),
    ensures
        forall|i: int| 0 <= i < k ==> s@[i] == s@[i],
        forall|i: int| k <= i < (s.len() - 1) as int ==> s@[i] == s@[i],
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn remove_element(s: &Vec<i32>, k: usize) -> (v: Vec<i32>)
    requires 
        k < s.len(),
    ensures
        v.len() == s.len() - 1,
        forall|i: int| 0 <= i < k ==> v[i] == s[i],
        forall|i: int| k <= i < v.len() ==> v[i] == s[(i + 1) as int],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn remove_element(s: &Vec<i32>, k: usize) -> (v: Vec<i32>)
    requires 
        k < s.len(),
    ensures
        v.len() == s.len() - 1,
        forall|i: int| 0 <= i < k ==> v@[i] == s@[i],
        forall|i: int| k <= i < v.len() ==> v@[i] == s@[(i + 1) as int],
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == if i <= k { i } else { i - 1 },
            forall|j: int| 0 <= j < result.len() ==> 
                if j < k as int { result@[j] == s@[j] } else { result@[j] == s@[(j + 1) as int] },
    {
        if i != k {
            result.push(s@[i]);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

fn main() {}
}