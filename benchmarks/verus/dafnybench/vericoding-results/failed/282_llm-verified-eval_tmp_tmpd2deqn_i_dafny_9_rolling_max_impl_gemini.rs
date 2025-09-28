// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof bodies */
proof fn lemma_isMax_singleton(x: int)
    ensures isMax(x, seq![x]),
{
    let s = seq![x];
    assert(s.contains(x));
    assert forall|i: int| 0 <= i < s.len() implies s[i] <= x by {
        assert(s[i] == x);
    };
}

proof fn lemma_max_updates(s: Seq<int>, old_max: int, new_val: int)
    requires
        isMax(old_max, s),
    ensures
        isMax(if new_val > old_max { new_val } else { old_max }, s.push(new_val)),
{
    let new_max = if new_val > old_max { new_val } else { old_max };
    let s_new = s.push(new_val);

    if new_val <= old_max {
        assert(s.contains(old_max));
        vstd::seq_lib::lemma_push_preserves_contains(s, new_val, old_max);
        assert(s_new.contains(old_max));
    }
    assert(s_new.contains(new_max));

    assert forall|k: int| 0 <= k < s_new.len() implies s_new[k] <= new_max by {
        if k < s.len() {
            assert(s[k] <= old_max);
            assert(old_max <= new_max);
        } else {
            assert(s_new[k] == new_val);
            assert(new_val <= new_max);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<int>) -> (result: Vec<int>)
    requires
        numbers.len() > 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 < i < result.len() ==> isMax(result[i], numbers@.subrange(0, i + 1)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no logical change, only updated comment */
    let mut result: Vec<int> = Vec::new();
    result.push(numbers[0]);

    proof {
        lemma_isMax_singleton(numbers[0]);
    }

    let mut current_max = numbers[0];
    let mut i: usize = 1;
    while i < numbers.len()
        invariant
            1 <= i <= numbers.len(),
            result.len() == i,
            isMax(current_max, numbers@.subrange(0, i as int)),
            forall|j: int| 0 <= j < i as int ==> isMax(result@[j], numbers@.subrange(0, j + 1)),
        decreases numbers.len() - i
    {
        proof {
            lemma_max_updates(numbers@.subrange(0, i as int), current_max, numbers@[i as int]);
        }

        if numbers[i] > current_max {
            current_max = numbers[i];
        }

        result.push(current_max);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}