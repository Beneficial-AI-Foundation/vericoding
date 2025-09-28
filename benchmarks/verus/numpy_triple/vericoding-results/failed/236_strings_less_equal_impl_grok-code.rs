// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn string_le(s1: String, s2: String) -> bool {
    s1 <= s2
}

fn exec_string_le(s1: &String, s2: &String) -> (r: bool)
    ensures
        r == string_le(*s1, *s2),
{
    let a = s1.as_str();
    let b = s2.as_str();
    let mut j = 0;
    while j < a.len().min(b.len())
    {
        let c1 = a.get(j);
        let c2 = b.get(j);
        if c1 < c2 { return true; }
        if c1 > c2 { return false; }
        j += 1;
    }
    a.len() <= b.len()
}
// </vc-helpers>

// <vc-spec>
spec fn string_le(s1: String, s2: String) -> bool;

fn less_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1@.len() == x2@.len(),
    ensures 
        result@.len() == x1@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == string_le(x1@[i], x2@[i]),
        forall|i: int| 0 <= i < result@.len() ==> (result@[i] == true <==> string_le(x1@[i], x2@[i])),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result@.len() ==> result@[i] == true,
        forall|i: int| 0 <= i < result@.len() ==> (string_le(x1@[i], x2@[i]) && string_le(x2@[i], x1@[i])) ==> x1@[i] == x2@[i],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j] == string_le(x1@[j], x2@[j])
        decreases x1.len() - i
    {
        let b = exec_string_le(&x1[i], &x2[i]);
        result.push(b);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}