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
proof fn same_remainder_implies_divisible_difference(x: int, y: int, d: int)
    requires
        d > 0,
        x % d == y % d,
    ensures
        (x - y) % d == 0
{
}

/* helper modified by LLM (iteration 4): Fixed type conversion and execution */
fn check_all_same_remainder_exec(n: usize, m: usize, d: i8, matrix: &Vec<Vec<i8>>) -> bool {
    let mut first_remainder: Option<i8> = None;
    
    for i in 0..n {
        for j in 0..m {
            let remainder = matrix[i][j] % d;
            match first_remainder {
                None => first_remainder = Some(remainder),
                Some(expected) => {
                    if remainder != expected {
                        return false;
                    }
                }
            }
        }
    }
    
    true
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
    /* code modified by LLM (iteration 4): Fixed type conversions and sequence operations */
    let ghost matrix_seq: Seq<Seq<int>> = matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int));
    
    if !check_all_same_remainder_exec(n as usize, m as usize, d, &matrix) {
        return -1;
    }
    
    let mut temp_vec: Vec<i64> = Vec::new();
    
    let mut i: usize = 0;
    while i < matrix.len() as usize
        invariant
            i <= matrix.len() as usize,
            temp_vec@ == flatten(matrix_seq).map(|x: int| x as i64)
    {
        let mut j: usize = 0;
        while j < matrix[i].len() as usize
            invariant
                j <= matrix[i].len() as usize,
                temp_vec@ == flatten(matrix_seq).subrange(0, temp_vec.len() as int).map(|x: int| x as i64)
        {
            temp_vec.push(matrix[i][j] as i64);
            j += 1;
        }
        i += 1;
    }
    
    let ghost temp_vec_seq: Seq<int> = temp_vec@.map(|i: int, x: i64| x as int);
    let mut simplified: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < temp_vec.len()
        invariant
            idx <= temp_vec.len(),
            simplified@ == divide_sequence_by_d(temp_vec_seq, d as int).map(|i: int, x: int| x as i64)
    {
        simplified.push(temp_vec[idx] / d as i64);
        idx += 1;
    }
    
    let ghost simplified_seq: Seq<int> = simplified@.map(|i: int, x: i64| x as int);
    let min_val = seq_min(simplified_seq);
    let max_val = seq_max(simplified_seq);
    
    let mut best_ops = i64::MAX;
    let mut target = min_val as i64;
    
    while target <= max_val as i64
        invariant
            target >= min_val as i64,
            target <= max_val as i64 + 1,
            best_ops >= 0,
            best_ops as int == min_ops_in_range(simplified_seq, min_val, target as int - 1)
    {
        let mut total_ops: i64 = 0;
        let mut k: usize = 0;
        
        while k < simplified.len()
            invariant
                k <= simplified.len(),
                total_ops as int == sum_abs_differences_from_target(simplified_seq.subrange(0, k as int), target as int)
        {
            let diff = if simplified[k] >= target { 
                simplified[k] - target
            } else { 
                target - simplified[k]
            };
            total_ops += diff;
            k += 1;
        }
        
        if total_ops < best_ops {
            best_ops = total_ops;
        }
        
        target += 1;
    }
    
    best_ops as i8
}
// </vc-code>


}

fn main() {}