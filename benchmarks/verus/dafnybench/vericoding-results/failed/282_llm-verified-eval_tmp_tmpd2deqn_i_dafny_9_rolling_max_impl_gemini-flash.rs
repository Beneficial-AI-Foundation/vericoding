use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
fn max_of_seq(s: Seq<int>) -> int
    requires
        s.len() > 0,
    ensures
        s.contains(max_of_seq(s)),
        forall|i: int| 0 <= i < s.len() ==> s[i] <= max_of_seq(s),
{
    if s.len() == 1 {
        s.index(0)
    } else {
        let first = s.index(0);
        let rest_max = max_of_seq(s.subrange(1, s.len()));
        if first >= rest_max {
            first
        } else {
            rest_max
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
    let mut result: Vec<int> = Vec::new();
    result.push(numbers[0]);

    let mut i = 1;
    while i < numbers.len()
        invariant
            0 < i <= numbers.len(),
            result.len() == i,
            forall|k: int| 0 < k < i ==> isMax(result[k], numbers@.subrange(0, k + 1)),
    {
        let current_max = max_of_seq(numbers@.subrange(0, (i + 1) as int));
        result.push(current_max);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}