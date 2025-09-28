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
    forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] != #[trigger] s[j]
}

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] < s[i + 1]
}

spec fn is_valid_combination(combo: Seq<int>, k: int, n: int) -> bool {
    combo.len() == k &&
    sum(combo) == n &&
    (forall|j: int| 0 <= j < combo.len() ==> 1 <= #[trigger] combo[j] <= 9) &&
    is_distinct(combo) &&
    is_sorted(combo)
}

spec fn is_valid_extension(temp: Seq<int>, combo: Seq<int>, k: int, n: int, start: int) -> bool {
    combo.len() == k &&
    sum(combo) == n &&
    (forall|j: int| 0 <= j < combo.len() ==> 1 <= #[trigger] combo[j] <= 9) &&
    is_distinct(combo) &&
    is_sorted(combo) &&
    combo.len() >= temp.len() &&
    (forall|i: int| 0 <= i < temp.len() ==> #[trigger] temp[i] == #[trigger] combo[i]) &&
    (forall|i: int| temp.len() <= i < combo.len() ==> #[trigger] combo[i] >= start)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Keep to_int_seq accepting Vec<i8> */
spec fn to_int_seq(v: Vec<i8>) -> Seq<int> {
    v@.map(|_, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn combination_sum3(k: i8, n: i8) -> (result: Vec<Vec<i8>>)
    requires k > 0 && n > 0 && k <= 9
    ensures 
        (forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == k as int) &&
        (forall|i: int| 0 <= i < result.len() ==> sum(to_int_seq(#[trigger] result[i])) == n as int) &&
        (forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < #[trigger] result[i].len() ==> 1 <= #[trigger] result[i][j] as int <= 9) &&
        (forall|i: int| 0 <= i < result.len() ==> is_distinct(to_int_seq(#[trigger] result[i]))) &&
        (forall|i: int| 0 <= i < result.len() ==> is_sorted(to_int_seq(#[trigger] result[i]))) &&
        (forall|i: int, j: int| 0 <= i < j < result.len() ==> to_int_seq(#[trigger] result[i]) != to_int_seq(#[trigger] result[j])) &&
        (forall|combo: Seq<int>| is_valid_combination(combo, k as int, n as int) ==> exists|i: int| 0 <= i < result.len() && to_int_seq(#[trigger] result[i]) == combo) &&
        (forall|i: int| 0 <= i < result.len() ==> is_valid_combination(to_int_seq(#[trigger] result[i]), k as int, n as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Clone temp when calling to_int_seq to fix type mismatch */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut temp: Vec<i8> = Vec::new();
    backtrack(&mut result, &mut temp, k, n, 1);
    result
}

fn backtrack(result: &mut Vec<Vec<i8>>, temp: &mut Vec<i8>, k: i8, n: i8, start: i8)
    requires
        k > 0,
        n >= 0,
        k <= 9,
        start >= 1,
        start <= 10,
        temp.len() <= k as int,
        forall|i: int| 0 <= i < temp.len() ==> 1 <= temp@[i] <= 9,
        forall|i: int| 0 <= i < temp.len() - 1 ==> temp@[i] < temp@[i + 1],
        is_distinct(to_int_seq(temp.clone())),
        is_sorted(to_int_seq(temp.clone())),
        forall|i: int| 0 <= i < result.len() ==> result@[i].len() == k as int,
        forall|i: int| 0 <= i < result.len() ==> sum(to_int_seq(result@[i])) == n as int,
        forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < result@[i].len() ==> 1 <= result@[i]@[j] <= 9,
        forall|i: int| 0 <= i < result.len() ==> is_distinct(to_int_seq(result@[i])),
        forall|i: int| 0 <= i < result.len() ==> is_sorted(to_int_seq(result@[i])),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> to_int_seq(result@[i]) != to_int_seq(result@[j]),
        forall|combo: Seq<int>| is_valid_extension(to_int_seq(temp.clone()), combo, k as int, n as int, start as int) ==> exists|i: int| 0 <= i < result.len() && to_int_seq(result@[i]) == combo,
    ensures
        temp@ == old(temp)@,
        forall|i: int| 0 <= i < old(result).len() ==> result@[i] == old(result)@[i],
        forall|i: int| 0 <= i < result.len() ==> result@[i].len() == k as int,
        forall|i: int| 0 <= i < result.len() ==> sum(to_int_seq(result@[i])) == n as int,
        forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < result@[i].len() ==> 1 <= result@[i]@[j] <= 9,
        forall|i: int| 0 <= i < result.len() ==> is_distinct(to_int_seq(result@[i])),
        forall|i: int| 0 <= i < result.len() ==> is_sorted(to_int_seq(result@[i])),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> to_int_seq(result@[i]) != to_int_seq(result@[j]),
        forall|combo: Seq<int>| is_valid_extension(to_int_seq(temp.clone()), combo, k as int, n as int, start as int) ==> exists|i: int| 0 <= i < result.len() && to_int_seq(result@[i]) == combo,
    decreases k - temp.len(), 10 - start
{
    if temp.len() == k as usize {
        let temp_sum = sum(to_int_seq(temp.clone()));
        if temp_sum == n as int {
            result.push(temp.clone());
        }
    } else if temp.len() < k as usize {
        let mut i = start;
        while i <= 9
            invariant
                k > 0,
                n >= 0,
                k <= 9,
                start >= 1,
                start <= 10,
                i >= start,
                i <= 10,
                temp.len() <= k as int,
                temp.len() < k as int,
                temp@ == old(temp)@,
                forall|j: int| 0 <= j < temp.len() ==> 1 <= temp@[j] <= 9,
                forall|j: int| 0 <= j < temp.len() - 1 ==> temp@[j] < temp@[j + 1],
                is_distinct(to_int_seq(temp.clone())),
                is_sorted(to_int_seq(temp.clone())),
                forall|j: int| 0 <= j < result.len() ==> result@[j].len() == k as int,
                forall|j: int| 0 <= j < result.len() ==> sum(to_int_seq(result@[j])) == n as int,
                forall|j: int| 0 <= j < result.len() ==> forall|l: int| 0 <= l < result@[j].len() ==> 1 <= result@[j]@[l] <= 9,
                forall|j: int| 0 <= j < result.len() ==> is_distinct(to_int_seq(result@[j])),
                forall|j: int| 0 <= j < result.len() ==> is_sorted(to_int_seq(result@[j])),
                forall|j: int, l: int| 0 <= j < l < result.len() ==> to_int_seq(result@[j]) != to_int_seq(result@[l]),
                forall|combo: Seq<int>| is_valid_extension(to_int_seq(temp.clone()), combo, k as int, n as int, i as int) ==> exists|j: int| 0 <= j < result.len() && to_int_seq(result@[j]) == combo,
            decreases 10 - i
        {
            temp.push(i);
            backtrack(result, temp, k, n - i, i + 1);
            temp.pop();
            i = i + 1;
        }
    }
}
// </vc-code>


}

fn main() {}