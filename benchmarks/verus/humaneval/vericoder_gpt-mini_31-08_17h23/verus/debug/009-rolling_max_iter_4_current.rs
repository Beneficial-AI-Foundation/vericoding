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
proof fn seq_max_take_snoc(a: Seq<i32>, i: int)
    requires 0 <= i && i < a.len()
    ensures seq_max(a.take(i+1)) == if a@[i] > seq_max(a.take(i)) { a@[i] } else { seq_max(a.take(i)) }
    decreases a.len()
{
    let s = a.take(i+1);
    // s.last() == a@[i] and s.drop_last() == a.take(i)
    assert(s.len() == i + 1);
    assert(s.last() == a@[i]);
    assert(s.drop_last() == a.take(i));
    // By definition of seq_max on non-empty sequence s
    assert(seq_max(s) == if s.last() > seq_max(s.drop_last()) { s.last() } else { seq_max(s.drop_last()) });
    // substitute equalities
    assert(seq_max(a.take(i+1)) == if a@[i] > seq_max(a.take(i)) { a@[i] } else { seq_max(a.take(i)) });
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
    // impl-start
    let mut result: Vec<i32> = Vec::new();
    let n: int = numbers.len() as int;
    let mut i: int = 0;
    let mut curr_max: i32 = i32::MIN; // seq_max(numbers@.take(0)) == i32::MIN

    // loop to build rolling maxima
    while i < n
        invariant 0 <= i && i <= n &&
                  result.len() as int == i &&
                  forall|j: int| 0 <= j && j < i ==> result[j] == seq_max(numbers@.take(j + 1)) &&
                  curr_max == seq_max(numbers@.take(i));
        decreases n - i
    {
        let idx: usize = i as usize;
        let cur: i32 = numbers.get(idx);
        let next: i32 = if cur > curr_max { cur } else { curr_max };

        // Prove that next == seq_max(numbers@.take(i+1))
        proof {
            // use lemma about seq_max on take(i+1)
            seq_max_take_snoc(numbers@, i);
            // by the loop invariant curr_max == seq_max(numbers@.take(i))
            assert(seq_max(numbers@.take(i+1)) ==
                   if numbers@[i] > seq_max(numbers@.take(i)) { numbers@[i] } else { seq_max(numbers@.take(i)) });
            assert(curr_max == seq_max(numbers@.take(i)));
            assert(seq_max(numbers@.take(i+1)) == if cur > curr_max { cur } else { curr_max });
            assert(seq_max(numbers@.take(i+1)) == next);
        }

        result.push(next);
        curr_max = next;
        i = i + 1;
    }

    result
    // impl-end
}
// </vc-code>

fn main() {}
}