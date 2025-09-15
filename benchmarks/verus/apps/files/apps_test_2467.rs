// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.subrange(1, s.len() as int))
    }
}

spec fn is_distinct(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> s[i] < s[i + 1]
}

spec fn is_valid_combination(combo: Seq<int>, k: int, n: int) -> bool {
    combo.len() == k &&
    sum(combo) == n &&
    (forall|j: int| 0 <= j < combo.len() ==> 1 <= combo[j] <= 9) &&
    is_distinct(combo) &&
    is_sorted(combo)
}

spec fn is_valid_extension(temp: Seq<int>, combo: Seq<int>, k: int, n: int, start: int) -> bool {
    combo.len() == k &&
    sum(combo) == n &&
    (forall|j: int| 0 <= j < combo.len() ==> 1 <= combo[j] <= 9) &&
    is_distinct(combo) &&
    is_sorted(combo) &&
    combo.len() >= temp.len() &&
    (forall|i: int| 0 <= i < temp.len() ==> temp[i] == combo[i]) &&
    (forall|i: int| temp.len() <= i < combo.len() ==> combo[i] >= start)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn combination_sum3(k: int, n: int) -> (result: Vec<Vec<int>>)
    requires k > 0 && n > 0 && k <= 9
    ensures (forall|i: int| 0 <= i < result.len() ==> result[i].len() == k) &&
            (forall|i: int| 0 <= i < result.len() ==> sum(result[i]@) == n) &&
            (forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < result[i].len() ==> 1 <= result[i][j] <= 9) &&
            (forall|i: int| 0 <= i < result.len() ==> is_distinct(result[i]@)) &&
            (forall|i: int| 0 <= i < result.len() ==> is_sorted(result[i]@)) &&
            (forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i]@ != result[j]@) &&
            (forall|combo: Seq<int>| is_valid_combination(combo, k, n) ==> exists|i: int| 0 <= i < result.len() && result[i]@ == combo) &&
            (forall|i: int| 0 <= i < result.len() ==> is_valid_combination(result[i]@, k, n))
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}