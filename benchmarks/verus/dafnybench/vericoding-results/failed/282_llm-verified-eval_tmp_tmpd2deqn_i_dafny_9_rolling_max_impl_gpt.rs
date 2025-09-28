use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
proof fn lemma_isMax_singleton_first(s: Seq<int>)
    requires
        s.len() > 0,
    ensures
        isMax(s[0], s.subrange(0, 1)),
{
    assert(s.subrange(0, 1).len() == 1);
    assert(s.subrange(0, 1).contains(s[0])) by {
        let j: int = 0;
        assert(0 <= j && j < s.subrange(0, 1).len());
        assert(s.subrange(0, 1)[j] == s[0]);
    }
    assert(forall|i: int| 0 <= i && i < s.subrange(0, 1).len() ==> #[trigger] s.subrange(0, 1)[i] <= s[0]) by {
        assert(s.subrange(0, 1).len() == 1);
        assert(s.subrange(0, 1)[0] == s[0]);
    }
}

proof fn lemma_subrange_snoc(s: Seq<int>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.subrange(0, i + 1) == s.subrange(0, i).push(s[i]),
{
    let s0 = s.subrange(0, i);
    let s1 = s.subrange(0, i + 1);
    assert(s0.len() == i);
    assert(s1.len() == i + 1);

    assert(s1 == s0.push(s[i])) by {
        assert(s0.push(s[i]).len() == s0.len() + 1);
        assert(s1.len() == s0.push(s[i]).len());

        assert forall|j: int|
            0 <= j && j < s1.len() ==> #[trigger] s1[j] == s0.push(s[i])[j]
        by {
            if j < i {
                assert(0 <= j && j < i);
                assert(s1[j] == s[j]);
                assert(s0[j] == s[j]);
                assert(s0.push(s[i])[j] == s0[j]);
            } else {
                assert(j == i);
                assert(s1[i] == s[i]);
                assert(s0.push(s[i])[s0.len()] == s[i]);
                assert(s0.len() == i);
                assert(s0.push(s[i])[i] == s[i]);
            }
        }
    }
}

proof fn lemma_isMax_push_kept(m: int, s: Seq<int>, x: int)
    requires
        isMax(m, s),
        x <= m,
    ensures
        isMax(m, s.push(x)),
{
    // contains
    let j = choose|j: int| 0 <= j && j < s.len() && #[trigger] s[j] == m;
    assert(s.push(x).contains(m)) by {
        assert(0 <= j && j < s.len());
        assert(j < s.push(x).len());
        assert(s.push(x)[j] == s[j]);
        assert(s[j] == m);
    }
    // bounds
    assert(forall|i: int| 0 <= i && i < s.push(x).len() ==> #[trigger] s.push(x)[i] <= m) by {
        assert(s.push(x).len() == s.len() + 1);
        assert forall|i: int|
            0 <= i && i < s.len() ==> #[trigger] s[i] <= m by {}
        if true {
            // proof done by the assertions above
        }
    }
}

proof fn lemma_isMax_push_new(m: int, s: Seq<int>, x: int)
    requires
        isMax(m, s),
        m <= x,
    ensures
        isMax(x, s.push(x)),
{
    // contains
    assert(s.push(x).contains(x)) by {
        let j: int = s.len();
        assert(0 <= j && j < s.push(x).len());
        assert(s.push(x)[j] == x);
    }
    // bounds
    assert(forall|i: int| 0 <= i && i < s.push(x).len() ==> #[trigger] s.push(x)[i] <= x) by {
        assert(s.push(x).len() == s.len() + 1);
        assert forall|i0: int|
            0 <= i0 && i0 < s.len() ==> #[trigger] s[i0] <= m by {}
        assert forall|i0: int|
            0 <= i0 && i0 < s.len() ==> #[trigger] s[i0] <= x
        by {
            assert(s[i0] <= m);
            assert(m <= x);
        }
        // last element equals x, hence <= x
        assert(s.push(x)[s.len()] == x);
    }
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
    let n: usize = numbers.len();
    let mut result: Vec<int> = Vec::new();
    let first = numbers[0];
    result.push(first);
    let mut cur_max = first;

    // Loop over remaining indices, maintaining the invariant that
    // for all processed positions j (0 < j < result.len()),
    // result[j] is the max of
// </vc-code>

fn main() {
}

}