// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper lemmas for proving count_occurrences properties
proof fn count_occurrences_append(s1: Seq<i32>, s2: Seq<i32>, x: i32)
    ensures count_occurrences(s1 + s2, x) == count_occurrences(s1, x) + count_occurrences(s2, x)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 == s2);
    } else {
        assert(s1 == s1.first() + s1.skip(1));
        count_occurrences_append(s1.skip(1), s2, x);
        assert((s1.first() + s1.skip(1)) + s2 == s1.first() + (s1.skip(1) + s2));
    }
}

proof fn count_occurrences_swap(seq: Seq<i32>, i: int, j: int, x: i32)
    requires 0 <= i < seq.len(), 0 <= j < seq.len()
    ensures count_occurrences(seq.update(i, seq[j]).update(j, seq[i]), x) == count_occurrences(seq, x)
{
    let temp_seq = seq.update(i, seq[j]);
    let final_seq = temp_seq.update(j, seq[i]);
    
    if i == j {
        assert(final_seq == seq);
    } else {
        // Need to show that swapping preserves count by induction
        count_occurrences_swap_lemma(seq, final_seq, i, j, x, 0);
    }
}

proof fn count_occurrences_swap_lemma(old_seq: Seq<i32>, new_seq: Seq<i32>, i: int, j: int, x: i32, k: int)
    requires
        0 <= i < old_seq.len(),
        0 <= j < old_seq.len(),
        i != j,
        new_seq.len() == old_seq.len(),
        new_seq[i] == old_seq[j],
        new_seq[j] == old_seq[i],
        forall|idx: int| 0 <= idx < old_seq.len() && idx != i && idx != j ==> new_seq[idx] == old_seq[idx],
        0 <= k <= old_seq.len()
    ensures count_occurrences(new_seq.take(k), x) == count_occurrences(old_seq.take(k), x)
    decreases old_seq.len() - k
{
    if k == 0 {
        assert(new_seq.take(0) == Seq::<i32>::empty());
        assert(old_seq.take(0) == Seq::<i32>::empty());
    } else if k <= old_seq.len() {
        count_occurrences_swap_lemma(old_seq, new_seq, i, j, x, k - 1);
    }
}

proof fn count_occurrences_update_same(seq: Seq<i32>, i: int, val: i32, x: i32)
    requires 0 <= i < seq.len(), seq[i] == val
    ensures count_occurrences(seq.update(i, val), x) == count_occurrences(seq, x)
{
    count_occurrences_update_same_lemma(seq, i, val, x, 0);
}

proof fn count_occurrences_update_same_lemma(seq: Seq<i32>, i: int, val: i32, x: i32, k: int)
    requires
        0 <= i < seq.len(),
        seq[i] == val,
        0 <= k <= seq.len()
    ensures count_occurrences(seq.update(i, val).take(k), x) == count_occurrences(seq.take(k), x)
    decreases seq.len() - k
{
    if k == 0 {
        // Base case
    } else if k <= seq.len() {
        count_occurrences_update_same_lemma(seq, i, val, x, k - 1);
    }
}

/* helper modified by LLM (iteration 5): improved lemma with proper inductive proof structure */
proof fn count_occurrences_swap_preserve(old_seq: Seq<i32>, new_seq: Seq<i32>, i: int, j: int)
    requires 
        0 <= i < old_seq.len(),
        0 <= j < old_seq.len(),
        new_seq.len() == old_seq.len(),
        new_seq[i] == old_seq[j],
        new_seq[j] == old_seq[i],
        forall|k: int| 0 <= k < old_seq.len() && k != i && k != j ==> new_seq[k] == old_seq[k]
    ensures
        forall|x: i32| count_occurrences(new_seq, x) == count_occurrences(old_seq, x)
{
    // Use the count_occurrences_swap lemma for each x
    let swap_seq = old_seq.update(i, old_seq[j]).update(j, old_seq[i]);
    assert(swap_seq == new_seq);
    
    // The property follows from count_occurrences_swap
    forall|x: i32| {
        count_occurrences_swap(old_seq, i, j, x);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(seq: Seq<i32>, x: i32) -> int
    decreases seq.len()
{
    if seq.len() == 0 {
        0int
    } else {
        (if seq[0] == x { 1int } else { 0int }) + count_occurrences(seq.skip(1), x)
    }
}

fn sort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        forall|x: i32| count_occurrences(result@, x) == count_occurrences(a@, x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): improved invariants with proper bounds checking */
    let mut result = a;
    let n = result.len();
    
    // Simple bubble sort implementation
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == n,
            n == a.len(),
            forall|x: i32| count_occurrences(result@, x) == count_occurrences(a@, x),
            forall|k1: int, k2: int| 0 <= k1 < k2 < i ==> result[k1 as int] <= result[k2 as int]
        decreases n - i
    {
        let mut j = 0;
        while j < n - 1
            invariant
                j <= n - 1,
                result.len() == n,
                n == a.len(),
                i < n,
                forall|x: i32| count_occurrences(result@, x) == count_occurrences(a@, x),
                forall|k1: int, k2: int| 0 <= k1 < k2 < i ==> result[k1 as int] <= result[k2 as int],
                forall|k: int| 0 <= k <= j && k < i ==> result[k as int] <= result[i as int]
            decreases n - 1 - j
        {
            if result[j] > result[j + 1] {
                let ghost old_seq = result@;
                let temp = result[j];
                result.set(j, result[j + 1]);
                result.set(j + 1, temp);
                
                proof {
                    count_occurrences_swap_preserve(old_seq, result@, j as int, (j + 1) as int);
                }
            }
            j += 1;
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}