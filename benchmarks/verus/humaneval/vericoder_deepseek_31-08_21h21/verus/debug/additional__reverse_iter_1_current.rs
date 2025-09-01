use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_reverse_index<A>(s: Seq<A>, i: int)
    requires
        0 <= i && i < s.len(),
    ensures
        s[s.len() - 1 - i] == s@.index(s.len() - 1 - i),
{
}

proof fn lemma_reverse_properties<A>(s: Seq<A>)
    ensures
        forall|i: int| 0 <= i && i < s.len() ==> s[s.len() - 1 - i] == s@.index(s.len() - 1 - i),
{
    assert forall|i: int| 0 <= i && i < s.len() implies s[s.len() - 1 - i] == s@.index(s.len() - 1 - i) by {
        lemma_reverse_index(s, i);
    };
}
// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    let mut result = Vec::with_capacity(len);
    let mut j: usize = len;
    
    while j > 0
        invariant
            result.len() == len - j,
            forall|k: int| 0 <= k && k < result.len() ==> result[k] == a[len - 1 - k],
            j <= len,
    {
        j = j - 1;
        result.push(a[j]);
    }
    
    proof {
        lemma_reverse_properties(a@);
    }
    
    result
}
// </vc-code>

fn main() {}
}