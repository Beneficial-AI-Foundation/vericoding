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
proof fn lemma_seq_max_eq_max(s: Seq<i32>)
    requires s.len() > 0
    ensures seq_max(s) == max(s.last(), seq_max(s.drop_last()))
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
                max(seq_max(a.take(i-1)), a@[i-1])
            }
{
    if i == 0 {
        // Base case: empty sequence
    } else {
        let b = a.take(i);
        lemma_seq_max_eq_max(b);
        assert(b.last() == a@[i-1]);
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
            current_max == seq_max(numbers@.take(i)),
            forall|j: int| 0 <= j < i ==> result@[j] == seq_max(numbers@.take(j+1)),
    {
        let next = numbers[i];
        current_max = max(current_max, next);
        result.push(current_max);
        proof {
            lemma_seq_max_take(numbers@, i+1);
            assert(current_max == seq_max(numbers@.take(i+1)));
            assert(result@[i] == current_max);
        }
    }
    result
}
// </vc-code>

fn main() {}
}