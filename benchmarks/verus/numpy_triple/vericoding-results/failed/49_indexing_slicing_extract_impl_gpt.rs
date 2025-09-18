// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): bounds for count_true (maintains non-negativity and upper bound by length) */
proof fn lemma_count_true_bounds(condition: Seq<bool>)
    ensures
        0 <= count_true(condition),
        count_true(condition) <= condition.len()
    decreases condition.len()
{
    if condition.len() == 0 {
        assert(count_true(condition) == 0int);
    } else {
        let len = condition.len();
        lemma_count_true_bounds(condition.skip(1));
        assert(condition.skip(1).len() == len - 1);
        if condition[0] {
            assert(count_true(condition) == 1int + count_true(condition.skip(1)));
            assert(0int <= count_true(condition.skip(1)));
            assert(0int <= count_true(condition));
            assert(count_true(condition.skip(1)) <= len - 1);
            assert(count_true(condition) <= 1int + (len - 1));
            assert(count_true(condition) <= len);
        } else {
            assert(count_true(condition) == count_true(condition.skip(1)));
            assert(0int <= count_true(condition.skip(1)));
            assert(0int <= count_true(condition));
            assert(count_true(condition) <= len - 1);
            assert(count_true(condition) <= len);
        }
    }
}

/* helper modified by LLM (iteration 3): step lemma for count_true over takes */
proof fn lemma_count_true_take_step(s: Seq<bool>, i: int)
    requires
        0 <= i < s.len()
    ensures
        count_true(s.take(i + 1)) == count_true(s.take(i)) + (if s[i] { 1int } else { 0int })
    decreases i
{
    if i == 0 {
        assert(s.take(1).len() == 1);
        assert(count_true(s.take(1)) == (if s.take(1)[0] { 1int } else { 0int }) + count_true(s.take(1).skip(1)));
        assert(s.take(1)[0] == s[0]);
        assert(s.take(1).skip(1).len() == 0);
        assert(count_true(s.take(1).skip(1)) == 0int);
        assert(count_true(s.take(0)) == 0int);
    } else {
        proof {
            assert(s.take(i + 1).len() == i + 1);
            assert(count_true(s.take(i + 1)) == (if s.take(i + 1)[0] { 1int } else { 0int }) + count_true(s.take(i + 1).skip(1)));
            assert(s.take(i + 1)[0] == s[0]);
            assert(s.take(i + 1).skip(1) == s.skip(1).take(i));
            assert(s.take(i).len() == i);
            assert(count_true(s.take(i)) == (if s[0] { 1int } else { 0int }) + count_true(s.skip(1).take(i - 1)));
            lemma_count_true_take_step(s.skip(1), i - 1);
            assert(s.skip(1)[i - 1] == s[i]);
            assert(count_true(s.skip(1).take(i))
                   == count_true(s.skip(1).take(i - 1)) + (if s.skip(1)[i - 1] { 1int } else { 0int }));
            assert(count_true(s.take(i + 1))
                   == (if s[0] { 1int } else { 0int }) + count_true(s.skip(1).take(i - 1)) + (if s[i] { 1int } else { 0int }));
            assert(count_true(s.take(i))
                   == (if s[0] { 1int } else { 0int }) + count_true(s.skip(1).take(i - 1)));
            assert(count_true(s.take(i + 1))
                   == count_true(s.take(i)) + (if s[i] { 1int } else { 0int }));
        }
    }
}

/* helper modified by LLM (iteration 3): take(len) equals the original sequence; fixed int/nat cast */
proof fn lemma_take_len_is_self<T>(s: Seq<T>)
    ensures s.take(s.len() as int) == s
{
    assert(s.take(s.len() as int).len() == s.len());
    assert forall |k:int| 0 <= k < s.len() implies s.take(s.len() as int)[k] == s[k] by { };
}
// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int 
    decreases condition.len()
{
    if condition.len() == 0 {
        0int
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn extract(condition: Vec<bool>, arr: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == arr.len(),
        count_true(condition@) >= 0,
    ensures
        result.len() == count_true(condition@),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == arr[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): two-pass approach using count of trues; fixed casts and added bridging asserts */
    let n: usize = arr.len();
    assert(condition.len() == n);

    // First pass: count number of true values in condition
    let mut cnt: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            cnt <= i,
            count_true(condition@.take(i as int)) == cnt as int,
        decreases (n - i) as int
    {
        let b = condition[i];
        if b {
            cnt = cnt + 1;
        }
        proof {
            assert(i < n);
            assert(i < condition.len());
            lemma_count_true_take_step(condition@, i as int);
            assert(condition@[i as int] == b);
            let pre = count_true(condition@.take(i as int));
            let step = if b { 1int } else { 0int };
            assert(count_true(condition@.take((i as int) + 1)) == pre + step);
            if b {
                assert((cnt as int) == (pre + 1int));
            } else {
                assert((cnt as int) == pre);
            }
        }
        i = i + 1;
    }
    assert(i == n);
    proof {
        assert(condition@.len() == condition.len() as int);
    }
    assert(cnt <= n);

    // Second pass: take the first cnt elements from arr
    let mut result: Vec<f32> = Vec::new();
    i = 0;
    while i < cnt
        invariant
            i <= cnt,
            cnt <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result@[j] == arr@[j],
        decreases (cnt - i) as int
    {
        assert(i < n);
        let v = arr[i];
        result.push(v);
        i = i + 1;
    }

    proof {
        assert(count_true(condition@.take(n as int)) == cnt as int);
        lemma_take_len_is_self(condition@);
        assert(condition@.len() == n as int);
        assert(condition@.take(n as int) == condition@);
        assert(count_true(condition@) == cnt as int);
    }

    result
}
// </vc-code>

}
fn main() {}