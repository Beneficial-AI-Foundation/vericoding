use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
fn in_array_exec(a: &Vec<i32>, x: i32) -> (result: bool)
    ensures
        result == in_array(a@, x),
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] != x,
        decreases a.len() - i,
    {
        if a[i] == x {
            return true;
        }
        i = i + 1;
    }
    false
}

proof fn lemma_in_array_append(s: Seq<i32>, x: i32)
    ensures
        in_array(s.push(x), x),
{
    let new_seq = s.push(x);
    let idx = s.len() as int;
    assert(0 <= idx < new_seq.len());
    assert(new_seq[idx] == x);
}

proof fn lemma_in_array_extend(s1: Seq<i32>, s2: Seq<i32>, x: i32)
    requires
        in_array(s1, x),
    ensures
        in_array(s1.add(s2), x),
{
    let combined = s1.add(s2);
    assert(exists|i: int| 0 <= i < s1.len() && s1[i] == x);
    let witness_idx = choose|i: int| 0 <= i < s1.len() && s1[i] == x;
    assert(0 <= witness_idx < combined.len());
    assert(combined[witness_idx] == s1[witness_idx]);
    assert(combined[witness_idx] == x);
}

proof fn lemma_no_duplicates_preserved(result: Vec<i32>, x: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        !in_array(result@, x),
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.push(x).len() ==> result@.push(x)[i] != result@.push(x)[j],
{
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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| #![auto] 0 <= k < result.len() ==> in_array(a@, result[k]),
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases a.len() - i,
    {
        let current = a[i];
        if !in_array_exec(&result, current) {
            proof {
                lemma_in_array_append(result@, current);
                lemma_no_duplicates_preserved(result, current);
            }
            result.push(current);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}