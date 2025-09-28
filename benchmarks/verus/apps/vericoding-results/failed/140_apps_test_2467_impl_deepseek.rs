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

spec fn is_valid_combo_vec(combo: Vec<i8>, k: int, n: int) -> bool {
    is_valid_combination(to_int_seq(combo), k, n)
}

proof fn combination_lemma(temp: Seq<int>, k: int, n: int, start: int)
    requires
        temp.len() <= k,
        forall|i: int| 0 <= i < temp.len() ==> 1 <= temp[i] <= 9,
        is_distinct(temp),
        is_sorted(temp),
        (forall|i: int| 0 <= i < temp.len() - 1 ==> temp[i] < start <= temp[i] + 1),
        sum(temp) <= n,
    ensures
        (exists|combo: Seq<int>| is_valid_extension(temp, combo, k, n, start)) ==> 
        (exists|combo: Seq<int>| is_valid_combination(combo, k, n) && 
         combo.subrange(0, temp.len() as int) =~= temp),
{
}

proof fn distinct_sorted_extension(temp: Seq<int>, start: int, value: int)
    requires
        temp.len() > 0,
        is_distinct(temp),
        is_sorted(temp),
        start <= value,
        (forall|i: int| 0 <= i < temp.len() - 1 ==> temp[i] < start <= temp[i] + 1),
    ensures
        is_distinct(temp.push(value)),
        is_sorted(temp.push(value)),
        (forall|i: int| 0 <= i < temp.len() - 1 ==> temp[i] < start <= temp[i] + 1),
{
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
    /* code modified by LLM (iteration 5): Replace while-let loop with explicit stack handling */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut temp: Vec<i8> = Vec::new();
    let start = 1;
    
    let mut stack: Vec<(i8, i8)> = Vec::new();
    stack.push((start, n));
    
    while !stack.is_empty() {
        let (current, remaining) = stack.pop().unwrap();
        
        if temp.len() as i8 == k {
            if remaining == 0 {
                let combo = temp.clone();
                result.push(combo);
            }
            if !temp.is_empty() {
                let last = temp.pop().unwrap();
                stack.push((last + 1, remaining + last));
            }
        } else if current <= 9 && remaining >= current {
            temp.push(current);
            stack.push((current + 1, remaining - current));
        } else if !temp.is_empty() {
            let last = temp.pop().unwrap();
            stack.push((last + 1, remaining + last));
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}