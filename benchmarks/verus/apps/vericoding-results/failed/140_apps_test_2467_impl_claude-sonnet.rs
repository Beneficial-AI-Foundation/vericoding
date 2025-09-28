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
/* helper modified by LLM (iteration 5): fixed syntax error in requires clause */
spec fn to_int_seq(v: Vec<i8>) -> Seq<int> {
    v@.map(|i: int, x: i8| x as int)
}

proof fn sum_extension(temp: Seq<int>, combo: Seq<int>)
    requires
        combo.len() >= temp.len(),
        forall|i: int| 0 <= i < temp.len() ==> temp[i] == combo[i]
    ensures
        sum(combo) == sum(temp) + sum(combo.subrange(temp.len() as int, combo.len() as int))
    decreases combo.len()
{
    if temp.len() == 0 {
        assert(sum(temp) == 0);
        assert(combo.subrange(0, combo.len() as int) == combo);
    } else {
        let temp_tail = temp.subrange(1, temp.len() as int);
        let combo_tail = combo.subrange(1, combo.len() as int);
        sum_extension(temp_tail, combo_tail);
    }
}

proof fn sum_append(s1: Seq<int>, s2: Seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 == s2);
    } else {
        let s1_tail = s1.subrange(1, s1.len() as int);
        sum_append(s1_tail, s2);
    }
}

fn backtrack(k: i8, n: i8, start: i8, temp: &mut Vec<i8>, result: &mut Vec<Vec<i8>>)
    requires
        k > 0,
        n > 0,
        k <= 9,
        1 <= start <= 9,
        temp.len() <= k as nat,
        sum(to_int_seq(*temp)) <= n as int,
        forall|j: int| 0 <= j < temp.len() ==> 1 <= temp[j] as int <= 9,
        is_distinct(to_int_seq(*temp)),
        is_sorted(to_int_seq(*temp)),
        temp.len() == 0 || temp[temp.len() - 1] as int < start as int
    ensures
        forall|combo: Seq<int>| is_valid_extension(to_int_seq(*old(temp)), combo, k as int, n as int, start as int) ==> 
            exists|i: int| old(result).len() <= i < result.len() && to_int_seq(result[i]) == combo
{
    if temp.len() == k {
        if sum(to_int_seq(*temp)) == n as int {
            result.push(temp.clone());
        }
        return;
    }
    
    let mut i = start;
    while i <= 9
        invariant
            1 <= i <= 10,
            k > 0,
            n > 0,
            k <= 9,
            start <= i,
            temp.len() <= k as nat,
            sum(to_int_seq(*temp)) <= n as int
    {
        if temp.len() < k && sum(to_int_seq(*temp)) + i as int <= n as int {
            temp.push(i);
            backtrack(k, n, i + 1, temp, result);
            temp.pop();
        }
        i += 1;
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
{
    /* code modified by LLM (iteration 5): implemented backtracking algorithm */
    let mut result = Vec::new();
    let mut temp = Vec::new();
    
    if k > 0 && n > 0 && k <= 9 {
        backtrack(k, n, 1, &mut temp, &mut result);
    }
    
    result
}
// </vc-code>


}

fn main() {}