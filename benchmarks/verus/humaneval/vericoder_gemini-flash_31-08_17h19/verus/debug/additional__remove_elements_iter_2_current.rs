use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
proof fn lemma_equal_values_in_seq(s: Seq<i32>, a: i32, b: i32, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        s[i] == a,
        s[j] == b,
        a == b,
    ensures
        s[i] == s[j],
{
    assert(s[i] == s[j]);
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    // post-conditions-start
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut c: Vec<i32> = Vec::new();
    let mut i: int = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
            forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < c.len() ==> c[idx_1] != c[idx_2],
            forall|idx: int| #[trigger] (c@)[idx] ==> 0 <= idx < c.len() && (exists|a_idx: int| 0 <= a_idx < i && a@[a_idx] == c[idx]),
    {
        let val = a[i];

        let mut found_in_b = false;
        let mut j: int = 0;
        
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                found_in_b == (exists|k: int| 0 <= k < j && b@[k] == val),
        {
            if b[j] == val {
                found_in_b = true;
            }
            j = j + 1;
        }

        let mut already_in_c = false;
        let mut k: int = 0;
        
        while k < c.len()
            invariant
                0 <= k <= c.len(),
                already_in_c == (exists|l: int| 0 <= l < k && c@[l] == val),
        {
            if c[k] == val {
                already_in_c = true;
            }
            k = k + 1;
        }

        if !found_in_b && !already_in_c {
            c.push(val);
        }
        i = i + 1;
    }
    c
}
// </vc-code>

fn main() {}
}