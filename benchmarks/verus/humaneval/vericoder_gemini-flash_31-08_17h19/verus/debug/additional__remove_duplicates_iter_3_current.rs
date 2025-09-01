use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
spec fn distinct(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

proof fn lemma_append_distinct_if_not_in_seq(s: Seq<i32>, x: i32)
    requires
        distinct(s),
        !in_array(s, x),
    ensures
        distinct(s.push(x)),
{
    assert forall|i: int, j: int| 0 <= i < j < s.push(x).len() implies s.push(x)[i] != s.push(x)[j] by {
        if j == s.len() { // appended element
            assert(i < s.len());
            assert(s.push(x)[j] == x);
            assert(s.push(x)[i] == s[i]);
            assert(!in_array(s, x) ==> s[i] != x);
        } else { // both i, j are in original sequence or only i is in original sequence
            assert(j < s.len());
            assert(s.push(x)[i] == s[i]);
            assert(s.push(x)[j] == s[j]);
            assert(distinct(s) ==> s[i] != s[j]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        a.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0; // Changed to int to match quantifiers
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> in_array(a@, result[k]),
            distinct(result@),
            forall|x_idx: int| #![trigger in_array(result@, result[x_idx])]
                0 <= x_idx < result.len() ==>
                exists|k: int| 0 <= k < i && a[k] == result[x_idx],
    {
        let current_val = a[i];
        let mut found_in_result = false;
        if i > 0 || result.len() > 0 { // Check if result is non-empty
            let mut j: int = 0; // Changed to int
            while j < result.len()
                invariant
                    0 <= j <= result.len(),
                    found_in_result == (exists|k: int| 0 <= k < j && result[k] == current_val),
                    forall|k: int| 0 <= k < result.len() ==> in_array(a@, result[k]),
                    distinct(result@),
            {
                if result[j] == current_val {
                    found_in_result = true;
                    break;
                }
                j = j + 1;
            }
        }
        if !found_in_result {
            result.push(current_val);
            proof {
                let s_prev = result@.sub(0, result@.len() as int - 1); // Use sub for Seq
                if result@.len() > 0 {
                    assert(distinct(s_prev));
                    assert(!in_array(s_prev, current_val));
                    lemma_append_distinct_if_not_in_seq(s_prev, current_val);
                } else {
                    assert(distinct(result@)); // Empty sequence is distinct
                }
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}