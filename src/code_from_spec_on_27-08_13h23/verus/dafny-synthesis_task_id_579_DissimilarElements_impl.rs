use vstd::prelude::*;

verus! {

spec fn in_array(a: &Vec<int>, x: int) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
spec fn contains_element(s: Seq<int>, x: int) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == x
}

proof fn seq_push_preserves_contains(s: Seq<int>, x: int, y: int)
    ensures
        contains_element(s, y) ==> contains_element(s.push(x), y),
        !contains_element(s, y) ==> (contains_element(s.push(x), y) == (x == y)),
{
    if contains_element(s, y) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == y;
        assert(0 <= i < s.push(x).len());
        assert(s.push(x)[i] == y);
    }
}

proof fn seq_contains_unique(s: Seq<int>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        i != j,
        s[i] == s[j],
    ensures
        false,
{
    if i < j {
        assert(s.subrange(0, j)@[i] == s[j]);
    } else {
        assert(s.subrange(0, i)@[j] == s[i]);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn dissimilar_elements(a: &Vec<int>, b: &Vec<int>) -> (result: Vec<int>)
    ensures
        // All elements in the output are either in a or b, but not in both or neither
        forall|x: int| result@.contains(x) ==> (in_array(a, x) != in_array(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn dissimilar_elements(a: &Vec<int>, b: &Vec<int>) -> (result: Vec<int>)
    ensures
        forall|x: int| result@.contains(x) ==> (in_array(a, x) != in_array(b, x)),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut res: Vec<int> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            forall|x: int| res@.contains(x) ==> (in_array(a, x) != in_array(b, x)),
            forall|k: int, l: int| 0 <= k < l < res.len() ==> res[k] != res[l],
            i <= a.len(),
    {
        let x = a[i];
        if !res@.contains(x) && (in_array(a, x) != in_array(b, x)) {
            res.push(x);
        }
        i = i + 1;
    }

    i = 0;
    while i < b.len()
        invariant
            forall|x: int| res@.contains(x) ==> (in_array(a, x) != in_array(b, x)),
            forall|k: int, l: int| 0 <= k < l < res.len() ==> res[k] != res[l],
            i <= b.len(),
    {
        let x = b[i];
        if !res@.contains(x) && (in_array(a, x) != in_array(b, x)) {
            res.push(x);
        }
        i = i + 1;
    }

    res
}
// </vc-code>

fn main() {}

}