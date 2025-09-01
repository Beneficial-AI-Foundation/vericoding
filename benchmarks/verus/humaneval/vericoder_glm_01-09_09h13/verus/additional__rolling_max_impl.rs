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

// <vc-helpers>
spec fn i32_max(a: i32, b: i32) -> (ret: i32) {
    if a > b { a } else { b }
}

proof fn lemma_seq_max_append(s: Seq<i32>, x: i32)
    ensures seq_max(s.push(x)) == i32_max(seq_max(s), x)
{
    if s.len() == 0 {
        assert(seq_max(s.push(x)) == x);
        assert(seq_max(s) == i32::MIN);
        assert(i32_max(seq_max(s), x) == x);
    } else {
        reveal(seq_max);
        assert(seq_max(s.push(x)) == 
            if (s.push(x)).last() > seq_max((s.push(x)).drop_last()) 
            then (s.push(x)).last() 
            else seq_max((s.push(x)).drop_last())
        );
        assert((s.push(x)).last() == x);
        assert((s.push(x)).drop_last() == s);
        assert(seq_max(s.push(x)) == 
            if x > seq_max(s) 
            then x 
            else seq_max(s)
        );
        reveal(i32_max);
        if x > seq_max(s) {
            assert(seq_max(s.push(x)) == x);
            assert(i32_max(seq_max(s), x) == x);
        } else {
            assert(seq_max(s.push(x)) == seq_max(s));
            assert(i32_max(seq_max(s), x) == seq_max(s));
        }
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
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    for j in 0..numbers.len()
        invariant
            0 <= (j as int) <= numbers.len() as int,
            result.len() == j,
            current_max == seq_max(numbers@.take(j as int)),
            forall| k: int | 0 <= k < (j as int) ==> result@[k] == seq_max(numbers@.take(k+1))
    {
        let element = numbers[j];
        proof {
            lemma_seq_max_append(numbers@.take(j as int), element);
        }
        current_max = if element > current_max { element } else { current_max };
        result.push(current_max);
    }
    result
}
// </vc-code>

fn main() {}
}