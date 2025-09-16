// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma to handle all cases including i32::MIN */
proof fn lemma_seq_max_take_relationship(s: Seq<i32>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        seq_max(s.take(i + 1)) == if i == 0 { s[0] } else if s[i] > seq_max(s.take(i)) { s[i] } else { seq_max(s.take(i)) },
    decreases i,
{
    if i == 0 {
        assert(s.take(1).len() == 1);
        assert(s.take(1) =~= seq![s[0]]);
        assert(s.take(1).last() == s[0]);
        assert(s.take(1).drop_last().len() == 0);
        assert(seq_max(s.take(1).drop_last()) == i32::MIN);
        if s[0] > i32::MIN {
            assert(s.take(1).last() > seq_max(s.take(1).drop_last()));
            assert(seq_max(s.take(1)) == s.take(1).last());
            assert(seq_max(s.take(1)) == s[0]);
        } else {
            assert(s[0] == i32::MIN);
            assert(!(s.take(1).last() > seq_max(s.take(1).drop_last())));
            assert(seq_max(s.take(1)) == seq_max(s.take(1).drop_last()));
            assert(seq_max(s.take(1)) == i32::MIN);
            assert(seq_max(s.take(1)) == s[0]);
        }
    } else {
        assert(s.take(i + 1).len() == i + 1);
        assert(s.take(i + 1).last() == s[i]);
        assert(s.take(i + 1).drop_last() =~= s.take(i));
        assert(seq_max(s.take(i + 1).drop_last()) == seq_max(s.take(i)));
        
        if s[i] > seq_max(s.take(i)) {
            assert(s.take(i + 1).last() > seq_max(s.take(i + 1).drop_last()));
            assert(seq_max(s.take(i + 1)) == s.take(i + 1).last());
            assert(seq_max(s.take(i + 1)) == s[i]);
        } else {
            assert(!(s.take(i + 1).last() > seq_max(s.take(i + 1).drop_last())));
            assert(seq_max(s.take(i + 1)) == seq_max(s.take(i + 1).drop_last()));
            assert(seq_max(s.take(i + 1)) == seq_max(s.take(i)));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)

    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use the fixed lemma that handles i32::MIN */
    let mut result = Vec::new();
    let mut i = 0;
    let mut current_max = i32::MIN;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
            i > 0 ==> current_max == seq_max(numbers@.take(i as int)),
        decreases numbers.len() - i
    {
        if i == 0 {
            current_max = numbers[i];
        } else {
            if numbers[i] > current_max {
                current_max = numbers[i];
            }
        }
        
        proof {
            lemma_seq_max_take_relationship(numbers@, i as int);
            assert(current_max == seq_max(numbers@.take((i + 1) as int)));
        }
        
        result.push(current_max);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}