use vstd::prelude::*;

verus! {

spec fn seq_max(a: Seq<i32>) -> (ret: i32)
    decreases a.len(),
{
    if a.len() == 0 {
        i32::MIN
    } else if a.last() > seq_max(a.drop_last()) {
        a.last()
    } else {
        seq_max(a.drop_last())
    }
}
// pure-end

// <vc-helpers>
spec fn max_i32(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

proof fn lemma_seq_max_eq_max(s: Seq<i32>)
    requires s.len() > 0
    ensures seq_max(s) == max_i32(s.last(), seq_max(s.drop_last()))
{
    if s.last() > seq_max(s.drop_last()) {
        assert(seq_max(s) == s.last());
    } else {
        assert(seq_max(s) == seq_max(s.drop_last()));
    }
}

proof fn lemma_seq_max_take(a: Seq<i32>, i: int)
    requires 0 <= i <= a.len()
    ensures 
        seq_max(a.take(i)) == 
            if i == 0 { 
                i32::MIN 
            } else { 
                max_i32(seq_max(a.take(i-1)), a.index(i-1))
            }
{
    if i == 0 {
        // Base case: empty sequence
    } else {
        let b = a.take(i);
        lemma_seq_max_eq_max(b);
        assert(b.last() == a.index(i-1));
        assert(b.drop_last() == a.take(i-1));
    }
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();
    if n == 0 {
        return Vec::new();
    }
    let mut result = Vec::new();
    let first = numbers[0];
    result.push(first);
    let mut current_max = first;

    for i in 1..n
        invariant
            result.len() == i,
            current_max == seq_max(numbers@.take(i as int)),
            forall|j: int| 0 <= j < i ==> result@[j] == seq_max(numbers@.take(j+1)),
    {
        let next = numbers[i];
        let old_current_max = current_max;
        current_max = if old_current_max > next { old_current_max } else { next };
        result.push(current_max);
        proof {
            lemma_seq_max_take(numbers@, (i+1) as int);
            // Show current_max equals max_i32(old_current_max, next)
            if old_current_max > next {
                assert(current_max == old_current_max);
                // When old > next: max_i32 returns old
                assert(max_i32(old_current_max, next) == old_current_max);
                assert(current_max == max_i32(old_current_max, next));
            } else {
                assert(current_max == next);
                // When old <= next: max_i32 returns next
                assert(max_i32(old_current_max, next) == next);
                assert(current_max == max_i32(old_current_max, next));
            }
            // By lemma: seq_max(take(i+1)) == max_i32(seq_max(take(i)), numbers[i])
            // And seq_max(take(i)) = old_current_max (by invariant)
            assert(max_i32(old_current_max, next) == seq_max(numbers@.take(i+1)));
            assert(current_max == seq_max(numbers@.take(i+1)));
            assert(result@[i as int] == current_max);
        }
    }
    result
}
// </vc-code>

fn main() {}
}