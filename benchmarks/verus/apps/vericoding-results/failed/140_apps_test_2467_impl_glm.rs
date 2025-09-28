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
spec fn to_int_seq(v: Vec<i8>) -> Seq<int> {
    v@.map(|i: int, x: i8| x as int)
}

/* helper modified by LLM (iteration 5): fixed loop by removing break and added specifications */
exec fn backtrack(start: i8, k: i8, n: i8) -> (result: Vec<Vec<i8>>)
    requires 1 <= start <= 10 && k >= 0 && n >= 0
    decreases k
    ensures
        (forall|i: int| 0 <= i < result.len() ==> 
            is_valid_combination(to_int_seq(#[trigger] result[i]), k, n) &&
            (result[i].len() > 0 ==> result[i][0] >= start)
        ) &&
        (forall|combo: Seq<int>| 
            is_valid_combination(combo, k, n) && (combo.len()==0 || combo[0] >= start)
            ==> exists|i: int| 0 <= i < result.len() && to_int_seq(#[trigger] result[i]) == combo
        )
{
    if k == 0 {
        if n == 0 {
            vec![vec![]]
        } else {
            vec![]
        }
    } else if n < start || start > 9 {
        vec![]
    } else {
        let mut results = Vec::new();
        for num in start..10 {
            if num <= n {
                let sub_results = backtrack(num + 1, k - 1, n - num);
                for mut combo in sub_results {
                    combo.insert(0, num);
                    results.push(combo);
                }
            }
        }
        results
    }
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
/* code modified by LLM (iteration 5): no changes, calling updated backtrack */
{
    backtrack(1, k, n)
}
// </vc-code>


}

fn main() {}