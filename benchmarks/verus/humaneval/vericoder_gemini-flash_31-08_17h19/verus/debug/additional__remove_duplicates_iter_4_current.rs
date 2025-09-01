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
            assert(i < s.len() && !in_array(s,x) && s[i] != x); // This needs to be shown, implies s[i] != x
        } else { // both i, j are in original sequence or only i is in original sequence
            assert(j < s.len());
            assert(s.push(x)[i] == s[i]);
            assert(s.push(x)[j] == s[j]);
            assert(distinct(s)); // This is given by precondition
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
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i as int <= a.len() as int,
            result.len() as int <= a.len() as int,
            forall|k: int| 0 <= k < result.len() ==> in_array(a@, result@[k]),
            distinct(result@),
            forall|x_idx: int| #![trigger in_array(result@, result@[x_idx])]
                0 <= x_idx < result.len() ==>
                exists|k: int| 0 <= k < i as int && a@[k] == result@[x_idx],
    {
        let current_val = a[i];
        let mut found_in_result = false;
        if i > 0 || result.len() > 0 {
            let mut j: usize = 0;
            while j < result.len()
                invariant
                    j as int <= result.len() as int,
                    found_in_result == (exists|k: int| 0 <= k < j as int && result@[k] == current_val),
                    forall|k: int| 0 <= k < result.len() ==> in_array(a@, result@[k]),
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
                assert(result@.len() > 0);
                let prev_len = result@.len() - 1;
                let s_prev = result@.sub(0, prev_len as int);
                if prev_len > 0 {
                    assert(distinct(s_prev));
                    assert(!in_array(s_prev, current_val)); // This is implied by the loop invariant.
                    lemma_append_distinct_if_not_in_seq(s_prev, current_val);
                } else {
                    assert(distinct(result@));
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