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
// <vc-helpers>
proof fn lemma_vec_get_eq_seq_elem(numbers: &Vec<i32>, i: int)
    requires 0 <= i && i < numbers.len()
    ensures numbers.get(i) == numbers@.get(i)
{
    // The correspondence between Vec and its snapshot Seq is built-in;
    // this assertion is provable directly.
    assert(numbers.get(i) == numbers@.get(i));
}

proof fn lemma_seq_max_take_snoc(numbers: Seq<i32>, k: nat)
    requires k < numbers.len()
    ensures seq_max(numbers.take(k + 1)) ==
        if numbers@[k] > seq_max(numbers.take(k)) { numbers@[k] } else { seq_max(numbers.take(k)) }
{
    // Unfold the definition of seq_max on numbers.take(k+1).
    reveal(seq_max);
    // numbers.take(k+1) is non-empty and its last element is numbers@[k],
    // its drop_last is numbers.take(k).
    assert(numbers.take(k + 1).len() == k + 1);
    assert(numbers.take(k + 1).last() == numbers@[k]);
    assert(numbers.take(k + 1).drop_last() == numbers.take(k));
    // Apply the definition of seq_max to numbers.take(k+1).
    assert(seq_max(numbers.take(k + 1)) ==
           if numbers.take(k + 1).last() > seq_max(numbers.take(k + 1).drop_last()) {
               numbers.take(k + 1).last()
           } else {
               seq_max(numbers.take(k + 1).drop_last())
           });
    // Substitute last and drop_last with the equalities above.
    assert(seq_max(numbers.take(k + 1)) ==
           if numbers@[k] > seq_max(numbers.take(k)) {
               numbers@[k]
           } else {
               seq_max(numbers.take(k))
           });
}
// </vc-helpers>
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
    // impl-start
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    let mut cur: i32 = i32::MIN;
    while i < numbers.len()
        invariant 0 <= i && i <= numbers.len()
        invariant result.len() == i
        invariant forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1))
        invariant cur == seq_max(numbers@.take(i))
        decreases numbers.len() - i
    {
        let x: i32 = numbers.get(i);
        // relate runtime access to snapshot seq
        lemma_vec_get_eq_seq_elem(&numbers, i);
        assert(x == numbers@.get(i));
        // compute new current max
        if x > cur {
            cur = x;
        } else {
            // cur stays the same
        }
        // prove cur now equals seq_max(numbers.take(i+1))
        lemma_seq_max_take_snoc(numbers@, i as nat);
        // after the conditional, cur equals the if-branch of the lemma
        // we need to connect numbers@.get(i) with numbers@[i] notation used in lemma
        assert(cur == seq_max(numbers@.take(i + 1)));
        result.push(cur);
        i += 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}