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
proof fn lemma_vec_get_eq_seq_elem(numbers: &Vec<i32>, i: nat)
    requires i < numbers.len()
    ensures numbers.get(i as int) == numbers@[i]
{
    assert(numbers.get(i as int) == numbers@[i]);
}

proof fn lemma_seq_get_index(numbers: Seq<i32>, i: nat)
    requires i < numbers.len()
    ensures numbers.get(i as int) == numbers@[i]
{
    assert(numbers.get(i as int) == numbers@[i]);
}

proof fn lemma_seq_max_take_snoc(numbers: Seq<i32>, k: nat)
    requires k < numbers.len()
    ensures seq_max(numbers.take(k + 1)) ==
        if numbers@[k] > seq_max(numbers.take(k)) { numbers@[k] } else { seq_max(numbers.take(k)) }
{
    reveal(seq_max);
    assert(numbers.take(k + 1).len() == k + 1);
    assert(numbers.take(k + 1).last() == numbers@[k]);
    assert(numbers.take(k + 1).drop_last() == numbers.take(k));
    assert(seq_max(numbers.take(k + 1)) ==
           if numbers.take(k + 1).last() > seq_max(numbers.take(k + 1).drop_last()) {
               numbers.take(k + 1).last()
           } else {
               seq_max(numbers.take(k + 1).drop_last())
           });
    assert(seq_max(numbers.take(k + 1)) ==
           if numbers@[k] > seq_max(numbers.take(k)) {
               numbers@[k]
           } else {
               seq_max(numbers.take(k))
           });
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
    let mut result: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    let mut cur: i32 = i32::MIN;
    while i < numbers.len()
        invariant i <= numbers.len() &&
                  result.len() == i &&
                  (forall|j: nat| j < i ==> result[j as int] == seq_max(numbers@.take(j + 1))) &&
                  cur == seq_max(numbers@.take(i));
        decreases numbers.len() - i;
    {
        let x: i32 = numbers.get(i as int);
        lemma_vec_get_eq_seq_elem(&numbers, i);
        assert(x == numbers@[i]);
        lemma_seq_get_index(numbers@, i);
        assert(x == numbers@[i]);

        let prev: i32 = cur;
        if x > prev {
            cur = x;
        } else {
            cur = prev;
        }

        assert(prev == seq_max(numbers@.take(i)));

        if x > prev {
            assert(cur == x);
        } else {
            assert(cur == prev);
        }
        assert(cur == if numbers@[i] > seq_max(numbers@.take(i)) { numbers@[i] } else { seq_max(numbers@.take(i)) });

        lemma_seq_max_take_snoc(numbers@, i);
        assert(cur == seq_max(numbers@.take(i + 1)));

        result.push(cur);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}