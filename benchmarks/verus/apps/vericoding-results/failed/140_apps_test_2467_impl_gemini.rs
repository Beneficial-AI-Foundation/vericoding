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

proof fn sum_add_lemma(s1: Seq<int>, s2: Seq<int>)
    ensures sum(s1.add(s2)) == sum(s1) + sum(s2)
    decreases s1.len()
{
    if s1.len() > 0 {
        sum_add_lemma(s1.subrange(1, s1.len() as int), s2);
    }
}

/* helper modified by LLM (iteration 2): changed parameter types from ghost `int` to executive `i8` */
fn find_combinations_recursive(k_rem: i8, n_rem: i8, start: i8) -> (result: Vec<Vec<i8>>)
    requires
        0 <= k_rem <= 9,
        0 <= n_rem,
        1 <= start <= 10,
    ensures
        (forall|i: int| 0 <= i < result.len() ==> {
            let s = to_int_seq(#[trigger] result[i]);
            s.len() == k_rem as int &&
            sum(s) == n_rem as int &&
            is_sorted(s) &&
            is_distinct(s) &&
            (forall|j: int| 0 <= j < s.len() ==> start as int <= #[trigger] s[j] <= 9)
        }),
        (forall|i: int, j: int| 0 <= i < j < result.len() ==> to_int_seq(#[trigger] result[i]) != to_int_seq(#[trigger] result[j])),
        (forall|s: Seq<int>|
            (
                s.len() == k_rem as int &&
                sum(s) == n_rem as int &&
                is_sorted(s) &&
                is_distinct(s) &&
                (forall|j: int| 0 <= j < s.len() ==> start as int <= #[trigger] s[j] <= 9)
            )
        ==>
            (exists|i: int| 0 <= i < result.len() && to_int_seq(result[i]) == s)
        ),
    decreases k_rem, 10 - start
{
    if k_rem == 0 {
        if n_rem == 0 {
            let mut res = Vec::new();
            res.push(Vec::new());
            return res;
        } else {
            return Vec::new();
        }
    }

    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i = start;
    while i <= 9
        invariant
            0 < k_rem <= 9,
            1 <= start <= 10,
            start <= i <= 10,
            (forall|idx: int| 0 <= idx < result.len() ==> {
                let s = to_int_seq(#[trigger] result[idx]);
                s.len() == k_rem as int && sum(s) == n_rem as int && is_sorted(s) && is_distinct(s) &&
                s.len() > 0 && start as int <= s[0] && s[0] < i as int
            }),
            (forall|idx1: int, idx2: int| 0 <= idx1 < idx2 < result.len() ==> to_int_seq(result[idx1]) != to_int_seq(result[idx2])),
            (forall|s: Seq<int>| (
                s.len() == k_rem as int && sum(s) == n_rem as int && is_sorted(s) && is_distinct(s) &&
                s.len() > 0 && start as int <= s[0] && s[0] < i as int
            ) ==> (exists|idx: int| 0 <= idx < result.len() && to_int_seq(result[idx]) == s)),
        decreases 10 - i
    {
        if n_rem >= i {
            let sub_result = find_combinations_recursive(k_rem - 1, n_rem - i, i + 1);
            let mut j: usize = 0;
            while j < sub_result.len()
                invariant
                    result.len() == old(result).len() + j,
                    (forall|idx: int| 0 <= idx < old(result).len() ==> result[idx] == old(result)[idx]),
                    (forall|idx: int| old(result).len() <= idx < result.len() ==> {
                        let s = to_int_seq(result[idx]);
                        let sub_idx = (idx - old(result).len()) as usize;
                        s == seq![i as int].add(to_int_seq(sub_result[sub_idx]))
                    }),
                decreases sub_result.len() - j
            {
                sum_add_lemma(seq![i as int], to_int_seq(sub_result[j]));
                let mut temp_combo = Vec::new();
                temp_combo.push(i);
                let mut suffix = sub_result[j].clone();
                temp_combo.append(&mut suffix);
                result.push(temp_combo);
                j = j + 1;
            }
        }
        i = i + 1;
    }
    result
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
    /* code modified by LLM (iteration 2): call helper with executive types, removing ghost casts */
    find_combinations_recursive(k, n, 1)
}
// </vc-code>


}

fn main() {}