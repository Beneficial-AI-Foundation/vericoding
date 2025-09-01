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

proof fn seq_max_monotonic(a: Seq<i32>, b: Seq<i32>) 
    requires
        a.len() <= b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == b[i],
    ensures
        seq_max(a) <= seq_max(b),
{
    if a.len() == 0 {
        assert(seq_max(a) == i32::MIN);
    } else if b.len() > a.len() {
        let max_b_prefix = seq_max(b.drop_last());
        if b.last() > max_b_prefix {
            assert(seq_max(b) == b.last());
            if b.last() >= seq_max(a) {
                assert(seq_max(a) <= seq_max(b));
            }
        } else {
            assert(seq_max(b) == max_b_prefix);
            seq_max_monotonic(a, b.drop_last());
            assert(seq_max(a) <= seq_max(b.drop_last()));
            assert(seq_max(b.drop_last()) == seq_max(b));
        }
    }
}

proof fn seq_max_take_lemma(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        seq_max(a.take(i + 1)) >= a[i],
        forall|j: int| 0 <= j <= i ==> a[j] <= seq_max(a.take(i + 1))),
{
    if i == 0 {
        assert(a.take(1) == seq![a[0]]);
        assert(seq_max(a.take(1)) == a[0]);
    } else {
        seq_max_take_lemma(a, i - 1);
        let prefix = a.take(i);
        let current_max = seq_max(prefix);
        if a[i] > current_max {
            assert(seq_max(a.take(i + 1)) == a[i]);
        } else {
            assert(seq_max(a.take(i + 1)) == current_max);
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
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            result.len() == i,
            current_max == if i == 0 { i32::MIN } else { seq_max(numbers@.take(i)) },
            forall|j: int| 0 <= j < i ==> result@[j] == seq_max(numbers@.take(j + 1)),
            i <= numbers.len(),
    {
        let num = numbers[i];
        if num > current_max {
            current_max = num;
        }
        result.push(current_max);
        proof {
            assert(result@.len() == i + 1);
            assert(forall|j: int| 0 <= j < i ==> result@[j] == seq_max(numbers@.take(j + 1)));
            seq_max_take_lemma(numbers@, i as int);
            assert(result@[i] == current_max);
            if i == 0 {
                assert(seq_max(numbers@.take(1)) == numbers@[0]);
            } else {
                seq_max_monotonic(numbers@.take(i), numbers@.take(i + 1));
                assert(seq_max(numbers@.take(i + 1)) >= current_max);
                assert(seq_max(numbers@.take(i + 1)) == current_max || seq_max(numbers@.take(i + 1)) == numbers@[i]);
            }
            assert(result@[i] == seq_max(numbers@.take(i + 1)));
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}