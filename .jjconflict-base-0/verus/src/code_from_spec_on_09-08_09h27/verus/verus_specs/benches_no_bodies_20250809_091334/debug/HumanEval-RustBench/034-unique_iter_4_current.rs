use vstd::prelude::*;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

proof fn swap_preserves_multiset_helper(s: Seq<i32>, i: int, j: int)
    // pre-conditions-start
    requires
        0 <= i < j < s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        (s.take(j + 1)).to_multiset() =~= s.take(i).to_multiset().add(
            s.subrange(i + 1, j).to_multiset(),
        ).insert(s.index(j)).insert(s.index(i)),
    // post-conditions-end
{
    // The sequence s.take(j + 1) contains elements from index 0 to j
    // We need to show this equals s.take(i) + s.subrange(i+1, j) + s[i] + s[j]
    
    // s.take(j + 1) = s.take(i) + s[i] + s.subrange(i+1, j) + s[j]
    // The multiset operation is commutative, so we can rearrange
    assert(s.take(j + 1) =~= s.take(i) + seq![s.index(i)] + s.subrange(i + 1, j) + seq![s.index(j)]);
}
// pure-end

proof fn swap_preserves_multiset(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int)
    // pre-conditions-start
    requires
        0 <= i < j < s1.len() == s2.len(),
        forall|x: int| 0 <= x < s1.len() && x != i && x != j ==> s1.index(x) == s2.index(x),
        s1.index(i) == s2.index(j),
        s1.index(j) == s2.index(i),
    // pre-conditions-end
    // post-conditions-start
    ensures
        s1.to_multiset() == s2.to_multiset(),
    // post-conditions-end
{
    // s1 and s2 are identical except at positions i and j where values are swapped
    // This preserves the multiset since we're just moving elements around
    assert(forall|k: int| 0 <= k < s1.len() ==> s1.to_multiset().count(s1.index(k)) > 0);
    assert(forall|k: int| 0 <= k < s2.len() ==> s2.to_multiset().count(s2.index(k)) > 0);
}
// pure-end

fn sort_seq(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < ret@.len() ==> ret@.index(i) <= ret@.index(j),
        ret@.len() == s@.len(),
        s@.to_multiset() == ret@.to_multiset(),
    // post-conditions-end
{
    let mut result = s.clone();
    let mut i = 0;
    
    while i < result.len()
        invariant
            result@.len() == s@.len(),
            s@.to_multiset() == result@.to_multiset(),
            forall|x: int, y: int| 0 <= x < y < i ==> result@.index(x) <= result@.index(y),
    {
        let mut j = i + 1;
        while j < result.len()
            invariant
                i < result.len(),
                result@.len() == s@.len(),
                s@.to_multiset() == result@.to_multiset(),
                forall|x: int, y: int| 0 <= x < y < i ==> result@.index(x) <= result@.index(y),
                forall|k: int| i < k < j ==> result@.index(i as int) <= result@.index(k),
        {
            if result[j] < result[i] {
                /* code modified by LLM (iteration 1): Fixed borrowing conflict by storing values in temporary variables first */
                let ghost old_result = result@;
                let temp_i = result[i];
                let temp_j = result[j];
                result.set(i, temp_j);
                result.set(j, temp_i);
                proof {
                    swap_preserves_multiset(old_result, result@, i as int, j as int);
                }
            }
            j += 1;
        }
        i += 1;
    }
    result
}

fn unique_sorted(s: Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] < result[y],
            forall|x: int| #![auto] 0 <= x < result.len() ==> s@.contains(result[x]),
            forall|x: int| 0 <= x < i ==> result@.contains(s[x]),
    {
        if result.len() == 0 || result[result.len() - 1] != s[i] {
            result.push(s[i]);
            proof {
                lemma_seq_contains_after_push(result@, s[i as int], s[i as int]);
            }
        }
        i += 1;
    }
    result
}

fn unique(s: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
{
    let sorted = sort_seq(&s);
    unique_sorted(sorted)
}

}
fn main() {}