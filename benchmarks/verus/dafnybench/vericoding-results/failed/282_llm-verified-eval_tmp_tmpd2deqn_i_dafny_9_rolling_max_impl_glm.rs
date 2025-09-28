use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

proof fn lemma_subrange_contains<T>(s: Seq<T>, x: T, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        s.subrange(i, j).contains(x) ==> s.contains(x),
{
    assert forall|x: T| s.subrange(i, j).contains(x) implies s.contains(x) by {
        if s.subrange(i, j).contains(x) {
            let k = choose|k: int| 0 <= k < s.subrange(i, j).len() && s.subrange(i, j)@[k] == x;
            assert s@[i + k] == x;
        }
    }
}

proof fn lemma_subrange_max(s: Seq<int>, i: int, j: int, m: int)
    requires
        0 <= i <= j <= s.len(),
        isMax(m, s.subrange(i, j)),
    ensures
        forall|k: int| i <= k < j ==> s[k] <= m,
{
    assert forall|k: int| 0 <= k < s.subrange(i, j).len() implies s.subrange(i, j)[k] <= m by {
        assert s.subrange(i, j)[k] == s[i + k];
    }
}

proof fn lemma_subrange_extension<T>(s: Seq<T>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len(),
    ensures
        s.subrange(i, j) + s.subrange(j, k) == s.subrange(i, k),
{
    assert forall|idx: int| 0 <= idx < s.subrange(i, k).len() implies 
        (s.subrange(i, j) + s.subrange(j, k))[idx] == s.subrange(i, k)[idx] by {
        if idx < s.subrange(i, j).len() {
            assert (s.subrange(i, j) + s.subrange(j, k))[idx] == s.subrange(i, j)[idx];
            assert s.subrange(i, k)[idx] == s.subrange(i, j)[idx];
        } else {
            let offset = idx - s.subrange(i, j).len();
            assert (s.subrange(i, j) + s.subrange(j, k))[idx] == s.subrange(j, k)[offset];
            assert s.subrange(i, k)[idx] == s[j + offset];
            assert s.subrange(j, k)[offset] == s[j + offset];
        }
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
    let mut result = Vec::new();
    let mut max_so_far = numbers@[0];
    result.push(max_so_far);
    let mut i = 1;
    
    while i < numbers.len()
        invariant
            1 <= i <= numbers.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> isMax(result@[k], numbers@.subrange(0, k+1)),
            max_so_far == result@[i-1],
    {
        let current = numbers@[i];
        let old_max_so_far = max_so_far;
        if current > max_so_far {
            max_so_far = current;
        }
        result.push(max_so_far);
        proof {
            if max_so_far == old_max_so_far {
                lemma_subrange_contains(numbers@, max_so_far, 0, i);
                assert(numbers@.subrange(0, i+1).contains(max_so_far));
                assert forall|k: int| 0 <= k < i+1 implies numbers@[k] <= max_so_far by {
                    if k < i {
                        assert(numbers@.subrange(0, i)[k] <= old_max_so_far);
                    } else {
                        assert(numbers@[k] == current);
                        assert(current <= max_so_far);
                    }
                }
            } else {
                assert(current == max_so_far);
                assert forall|k: int| 0 <= k < i+1 implies numbers@[k] <= current by {
                    if k < i {
                        assert(numbers@[k] <= old_max_so_far);
                        assert(old_max_so_far < current);
                    } else {
                        assert(numbers@[k] == current);
                    }
                }
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}