// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): maintained step lemma for count_true over take; minor comment update */
proof fn lemma_count_true_take_step(s: Seq<bool>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        count_true(s.take(i + 1)) == count_true(s.take(i)) + (if s[i] { 1int } else { 0int }),
    decreases i
{
    if i == 0 {
        assert(s.len() > 0);
        assert(s.take(1).len() == 1);
        assert(s.take(1)[0] == s[0]);
        assert(s.take(1).skip(1).len() == 0);
        assert(count_true(s.take(1)) == (if s.take(1)[0] { 1int } else { 0int }) + count_true(s.take(1).skip(1)));
        assert(count_true(s.take(1).skip(1)) == 0int);
        assert(count_true(s.take(0)) == 0int);
        assert(count_true(s.take(1)) == (if s[0] { 1int } else { 0int }));
        assert(count_true(s.take(1)) == count_true(s.take(0)) + (if s[0] { 1int } else { 0int }));
    } else {
        assert(i > 0);
        assert(s.take(i + 1).len() == i + 1);
        assert(count_true(s.take(i + 1)) == (if s.take(i + 1)[0] { 1int } else { 0int }) + count_true(s.take(i + 1).skip(1)));
        assert(s.take(i + 1)[0] == s[0]);
        assert(s.take(i + 1).skip(1) == s.skip(1).take(i));
        assert(s.take(i).len() == i);
        assert(count_true(s.take(i)) == (if s.take(i)[0] { 1int } else { 0int }) + count_true(s.take(i).skip(1)));
        assert(s.take(i)[0] == s[0]);
        assert(s.take(i).skip(1) == s.skip(1).take(i - 1));
        assert(s.skip(1).len() == s.len() - 1);
        assert(0 <= i - 1 < s.skip(1).len());
        lemma_count_true_take_step(s.skip(1), i - 1);
        assert(s.skip(1)[i - 1] == s[i]);
        assert(count_true(s.take(i + 1)) == count_true(s.take(i)) + (if s[i] { 1int } else { 0int }));
    }
}

// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int
    decreases condition.len()
{
    if condition.len() == 0 {
        0
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn compress(condition: Vec<bool>, a: Vec<f32>) -> (result: Vec<f32>)
    requires condition.len() == a.len(),
    ensures
        result.len() == count_true(condition@),
        exists|mapping: Seq<int>|
            mapping.len() == result.len() &&
            (forall|i: int| 0 <= i < mapping.len() ==> 
                0 <= mapping[i] < condition.len() &&
                condition@[mapping[i]] == true) &&
            (forall|i: int| 0 <= i < result.len() ==> 
                result@[i] == a@[mapping[i]]) &&
            (forall|i: int, j: int| 0 <= i < j < mapping.len() ==> 
                mapping[i] < mapping[j]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added trigger annotation on map access in invariant to resolve trigger inference error */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    let mut map: Ghost<Seq<int>> = Ghost(Seq::empty());

    while i < condition.len()
        invariant
            i <= condition.len(),
            a.len() == condition.len(),
            0 <= i as int <= condition.len() as int,
            map@.len() == result.len(),
            forall|k: int| 0 <= k < map@.len() ==> 0 <= #[trigger] map@[k] < i as int,
            forall|k: int| 0 <= k < map@.len() ==> condition@[map@[k]] == true,
            forall|k: int, l: int| 0 <= k < l < map@.len() ==> map@[k] < map@[l],
            forall|k: int| 0 <= k < result.len() ==> result@[k] == a@[map@[k]],
            map@.len() == count_true(condition@.take(i as int)),
        decreases condition.len() - i
    {
        if condition[i] {
            let v = a[i];
            result.push(v);
            map = Ghost(map@.push(i as int));
            proof {
                lemma_count_true_take_step(condition@, i as int);
            }
        } else {
            proof {
                lemma_count_true_take_step(condition@, i as int);
            }
        }
        i = i + 1;
    }

    proof {
        assert(i == condition.len());
        assert(condition@.len() == condition.len());
        assert(condition@.take(condition.len() as int) == condition@);
    }

    result
}
// </vc-code>

}
fn main() {}