// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int, d: int, matrix: Seq<Seq<int>>) -> bool {
    n > 0 && m > 0 && d > 0 &&
    matrix.len() == n &&
    (forall|i: int| #![auto] 0 <= i < n ==> matrix[i].len() == m) &&
    (forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> matrix[i][j] > 0)
}

spec fn all_same_remainder(matrix: Seq<Seq<int>>, d: int) -> bool
    recommends valid_input(matrix.len() as int, if matrix.len() > 0 { matrix[0].len() as int } else { 0 }, d, matrix)
{
    forall|i: int, j: int, k: int, l: int| 
        0 <= i < matrix.len() && 0 <= j < matrix[0].len() && 
        0 <= k < matrix.len() && 0 <= l < matrix[0].len() ==>
        matrix[i][j] % d == matrix[k][l] % d
}

spec fn flatten(matrix: Seq<Seq<int>>) -> Seq<int>
    decreases matrix.len()
{
    if matrix.len() == 0 {
        seq![]
    } else {
        matrix[0].add(flatten(matrix.subrange(1, matrix.len() as int)))
    }
}

spec fn divide_sequence_by_d(s: Seq<int>, d: int) -> Seq<int>
    recommends d > 0
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        seq![s[0] / d].add(divide_sequence_by_d(s.subrange(1, s.len() as int), d))
    }
}

spec fn sum_abs_differences_from_target(s: Seq<int>, target: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] >= target { s[0] - target } else { target - s[0] }) + 
        sum_abs_differences_from_target(s.subrange(1, s.len() as int), target)
    }
}

spec fn seq_min(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else if s.len() == 0 {
        0
    } else {
        let rest_min = seq_min(s.subrange(1, s.len() as int));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}

spec fn seq_max(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else if s.len() == 0 {
        0
    } else {
        let rest_max = seq_max(s.subrange(1, s.len() as int));
        if s[0] >= rest_max { s[0] } else { rest_max }
    }
}

spec fn min_ops_in_range(simplified: Seq<int>, min_val: int, max_val: int) -> int
    recommends simplified.len() > 0
    decreases max_val - min_val
{
    if min_val >= max_val {
        sum_abs_differences_from_target(simplified, min_val)
    } else {
        let mid = (min_val + max_val) / 2;
        let mid_ops = sum_abs_differences_from_target(simplified, mid);
        let left_ops = if mid > min_val { min_ops_in_range(simplified, min_val, mid - 1) } else { mid_ops };
        let right_ops = if mid < max_val { min_ops_in_range(simplified, mid + 1, max_val) } else { mid_ops };
        if mid_ops <= left_ops && mid_ops <= right_ops {
            mid_ops
        } else if left_ops <= right_ops {
            left_ops
        } else {
            right_ops
        }
    }
}

spec fn minimum_operations_to_make_equal(simplified: Seq<int>) -> int
    recommends simplified.len() > 0
{
    let min_val = seq_min(simplified);
    let max_val = seq_max(simplified);
    min_ops_in_range(simplified, min_val, max_val)
}
// </vc-preamble>

// <vc-helpers>
exec fn check_remainders(matrix: &[Vec<i8>], d: i8) -> Option<i8> {
    if matrix.len() == 0 || matrix[0].len() == 0 {
        return Some(0);
    }
    let r0 = matrix[0][0] % d;
    let mut i = 0;
    while i < matrix.len() {
        let mut j = 0;
        while j < matrix[i].len() {
            if matrix[i][j] % d != r0 {
                return None;
            }
            j += 1;
        }
        i += 1;
    }
    Some(r0)
}

exec fn collect_simplified(matrix: &[Vec<i8>], d: i8) -> Vec<i8> {
    let mut res = Vec::new();
    let mut i = 0;
    while i < matrix.len() {
        let mut j = 0;
        while j < matrix[i].len() {
            res.push(matrix[i][j] / d);
            j += 1;
        }
        i += 1;
    }
    res
}

exec fn min_of_vec(v: &[i8]) -> i8 {
    assert(v.len() > 0);
    let mut min = v[0];
    let mut i = 1;
    while i < v.len() {
        if v[i] < min {
            min = v[i];
        }
        i += 1;
    }
    min
}

exec fn max_of_vec(v: &[i8]) -> i8 {
    assert(v.len() > 0);
    let mut max = v[0];
    let mut i = 1;
    while i < v.len() {
        if v[i] > max {
            max = v[i];
        }
        i += 1;
    }
    max
}

exec fn sum_abs_for_target(simp: &[i8], target: i8) -> i32 {
    let mut sum: i32 = 0;
    let mut i = 0;
    while i < simp.len() {
        let diff = if simp[i] >= target { simp[i] - target } else { target - simp[i] };
        sum += diff as i32;
        i += 1;
    }
    sum
}

/* helper modified by LLM (iteration 2): fixed while loop syntax with proper invariant and decreases placement */
exec fn min_sum_abs(simp: &[i8]) -> i32 {
    let min_v = min_of_vec(simp);
    let max_v = max_of_vec(simp);
    let mut min_sum: i32 = i32::MAX;
    let mut current = min_v;
    while current <= max_v
        invariant
            current >= min_v,
            current <= max_v + 1,
            min_sum >= 0,
        decreases (max_v - current) as int
    {
        let current_sum = sum_abs_for_target(simp, current);
        if current_sum < min_sum {
            min_sum = current_sum;
        }
        current = current + 1;
    }
    if min_sum == i32::MAX {
        sum_abs_for_target(simp, min_v)
    } else {
        min_sum
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, d: i8, matrix: Vec<Vec<i8>>) -> (result: i8)
    requires valid_input(n as int, m as int, d as int, matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)))
    ensures 
        result == -1 <==> !all_same_remainder(matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)), d as int),
        result >= 0 ==> all_same_remainder(matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)), d as int),
        result >= 0 ==> {
            let flat = flatten(matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)));
            let simplified = divide_sequence_by_d(flat, d as int);
            result as int == minimum_operations_to_make_equal(simplified)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented solve function by calling helper functions to compute result */
    let common_r = check_remainders(&matrix, d);
    if common_r.is_none() {
        return -1;
    }
    let simp = collect_simplified(&matrix, d);
    let min_ops = min_sum_abs(&simp);
    min_ops as i8
}
// </vc-code>


}

fn main() {}