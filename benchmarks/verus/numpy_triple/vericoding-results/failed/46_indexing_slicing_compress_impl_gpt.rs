// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): step lemma for count_true over take prefixes with proper int casts */
proof fn count_true_take_step(s: Seq<bool>, k: int)
    requires 0 <= k < s.len() as int,
    ensures count_true(s.take(k + 1)) == count_true(s.take(k)) + (if s[k] { 1int } else { 0int })
{
    if k == 0 {
        assert((s.take(1)).len() as int == 1);
        assert(s.take(1)[0] == s[0]);
        assert(((s.take(1)).skip(1)).len() as int == 0);
        assert((s.take(0)).len() as int == 0);
        assert(count_true((s.take(1)).skip(1)) == 0);
        assert(count_true(s.take(0)) == 0);
        assert(count_true(s.take(1)) == (if s.take(1)[0] { 1int } else { 0int }) + count_true((s.take(1)).skip(1)));
        assert(count_true(s.take(1)) == (if s[0] { 1int } else { 0int }) + count_true(s.take(0)));
    } else {
        assert(s.take(k + 1)[0] == s[0]);
        assert((s.take(k + 1)).skip(1) == s.skip(1).take(k));
        assert(s.take(k)[0] == s[0]);
        assert((s.take(k)).skip(1) == s.skip(1).take(k - 1));

        assert(0 <= k - 1);
        assert((s.skip(1)).len() as int == (s.len() as int) - 1);
        assert(k - 1 < (s.skip(1)).len() as int);

        count_true_take_step(s.skip(1), k - 1);
        assert(s.skip(1)[k - 1] == s[k]);

        assert(count_true(s.take(k + 1)) == (if s.take(k + 1)[0] { 1int } else { 0int }) + count_true((s.take(k + 1)).skip(1)));
        assert(count_true(s.take(k + 1)) == (if s[0] { 1int } else { 0int }) + count_true(s.skip(1).take(k)));
        assert(count_true(s.take(k)) == (if s.take(k)[0] { 1int } else { 0int }) + count_true((s.take(k)).skip(1)));
        assert(count_true(s.take(k)) == (if s[0] { 1int } else { 0int }) + count_true(s.skip(1).take(k - 1)));
        assert(count_true(s.skip(1).take(k)) == count_true(s.skip(1).take(k - 1)) + (if s[k] { 1int } else { 0int }));
        assert(count_true(s.take(k + 1)) == count_true(s.take(k)) + (if s[k] { 1int } else { 0int }));
    }
}

/* helper modified by LLM (iteration 5): lemma that count_true over full take equals the original sequence */
proof fn count_true_take_full(s: Seq<bool>)
    ensures count_true(s.take(s.len() as int)) == count_true(s)
{
    if s.len() == 0 {
        assert((s.take(0)).len() as int == 0);
        assert(count_true(s.take(0)) == 0);
        assert(count_true(s) == 0);
    } else {
        assert((s.len() as int) > 0);
        assert(s.take(s.len() as int)[0] == s[0]);
        assert((s.take(s.len() as int)).skip(1) == s.skip(1).take((s.len() as int) - 1));
        assert((s.skip(1)).len() as int == (s.len() as int) - 1);

        count_true_take_full(s.skip(1));

        assert(count_true(s.take(s.len() as int)) ==
            (if s[0] { 1int } else { 0int }) +
            count_true(s.skip(1).take((s.len() as int) - 1)));

        assert(count_true(s.skip(1).take(((s.skip(1)).len()) as int)) == count_true(s.skip(1)));
        assert(count_true(s.skip(1).take((s.len() as int) - 1)) == count_true(s.skip(1)));

        assert(count_true(s) == (if s[0] { 1int } else { 0int }) + count_true(s.skip(1)));
        assert(count_true(s.take(s.len() as int)) == count_true(s));
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
    /* code modified by LLM (iteration 5): fixed @-method parentheses, used lemma to relate count_true of full take, and tightened int/nat casts */
    let n = condition.len();
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    let mut mapping: Ghost<Seq<int>> = Ghost(Seq::empty());

    while i < n
        invariant
            i <= n,
            result.len() == count_true((condition@).take(i as int)),
            (mapping@).len() == result.len(),
            forall|j: int| 0 <= j < (mapping@).len() as int ==>
                0 <= (mapping@)[j] < i as int &&
                (condition@)[(mapping@)[j]] == true &&
                result@[j] == a@[(mapping@)[j]],
            forall|p: int, q: int| 0 <= p < q < (mapping@).len() as int ==> (mapping@)[p] < (mapping@)[q],
            n == condition.len(),
            n == a.len()
        decreases (n as int) - (i as int)
    {
        proof {
            assert(0 <= i as int);
            assert(i < n);
            assert(i as int < (condition@).len() as int);
        }
        if condition[i] {
            let v = a[i];
            result.push(v);
            mapping = Ghost((mapping@).push(i as int));
            proof {
                count_true_take_step(condition@, i as int);
            }
        } else {
            proof {
                count_true_take_step(condition@, i as int);
            }
        }
        i = i + 1;
    }

    proof {
        assert(i == n);
        assert(result.len() == count_true((condition@).take(n as int)));
        count_true_take_full(condition@);
        assert(count_true((condition@).take(n as int)) == count_true(condition@));
    }

    proof {
        let m = mapping@;
        assert(m.len() == result.len());
        assert(forall|j: int| 0 <= j < m.len() ==> 0 <= m[j] < condition.len());
        assert(forall|j: int| 0 <= j < m.len() ==> (condition@)[m[j]] == true);
        assert(forall|j: int| 0 <= j < result.len() ==> result@[j] == a@[m[j]]);
        assert(forall|p: int, q: int| 0 <= p < q < m.len() ==> m[p] < m[q]);
        assert(exists|mapping_w: Seq<int>|
            mapping_w.len() == result.len() &&
            (forall|j: int| 0 <= j < mapping_w.len() ==> 0 <= mapping_w[j] < condition.len() && (condition@)[mapping_w[j]] == true) &&
            (forall|j: int| 0 <= j < result.len() ==> result@[j] == a@[mapping_w[j]]) &&
            (forall|p: int, q: int| 0 <= p < q < mapping_w.len() ==> mapping_w[p] < mapping_w[q])
        );
    }

    result
}
// </vc-code>

}
fn main() {}