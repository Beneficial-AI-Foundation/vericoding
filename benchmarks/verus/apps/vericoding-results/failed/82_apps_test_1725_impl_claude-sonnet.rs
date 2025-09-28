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
/* helper modified by LLM (iteration 5): fixed bounds checking and overflow handling */
fn check_same_remainder(matrix: &Vec<Vec<i8>>, d: i8) -> (result: bool)
    requires
        matrix@.len() > 0,
        d > 0,
        forall|i: int| #![auto] 0 <= i < matrix@.len() ==> matrix@[i]@.len() > 0
    ensures
        result == all_same_remainder(matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)), d as int)
{
    let first_remainder = matrix[0][0] % d;
    let mut i = 0;
    while i < matrix.len()
        invariant
            0 <= i <= matrix@.len(),
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < matrix@[ii]@.len() ==> matrix@[ii][jj] % d == first_remainder
        decreases matrix@.len() - i
    {
        let mut j = 0;
        while j < matrix[i].len()
            invariant
                0 <= i < matrix@.len(),
                0 <= j <= matrix@[i as int]@.len(),
                forall|jj: int| 0 <= jj < j ==> matrix@[i as int][jj] % d == first_remainder,
                forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < matrix@[ii]@.len() ==> matrix@[ii][jj] % d == first_remainder
            decreases matrix@[i as int]@.len() - j
        {
            if matrix[i][j] % d != first_remainder {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

fn compute_min_ops(values: Vec<i8>) -> (result: i8)
    requires values@.len() > 0
{
    let mut min_val = values[0];
    let mut max_val = values[0];
    let mut i = 1;
    
    while i < values.len()
        invariant
            1 <= i <= values@.len()
        decreases values@.len() - i
    {
        if values[i] < min_val {
            min_val = values[i];
        }
        if values[i] > max_val {
            max_val = values[i];
        }
        i += 1;
    }
    
    let mut best_ops: i8 = 127;
    let mut target = min_val;
    
    while target <= max_val
        invariant
            min_val <= target <= max_val + 1,
            best_ops >= 0
        decreases max_val - target + 1
    {
        let mut ops: i8 = 0;
        let mut j = 0;
        
        while j < values.len()
            invariant 
                0 <= j <= values@.len(),
                ops >= 0
            decreases values@.len() - j
        {
            let diff = if values[j] >= target { 
                (values[j] - target) as i8
            } else { 
                (target - values[j]) as i8
            };
            if ops <= 127 - diff {
                ops = ops + diff;
            } else {
                ops = 127;
                break;
            }
            j += 1;
        }
        
        if ops < best_ops {
            best_ops = ops;
        }
        
        if target == 127 { break; }
        target = target + 1;
    }
    
    best_ops
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
    /* code modified by LLM (iteration 5): added bounds checking invariants */
    if !check_same_remainder(&matrix, d) {
        return -1;
    }
    
    let mut flat_values = Vec::new();
    let mut i = 0;
    
    while i < matrix.len()
        invariant 
            0 <= i <= matrix@.len(),
            matrix@.len() > 0,
            forall|ii: int| #![auto] 0 <= ii < matrix@.len() ==> matrix@[ii]@.len() > 0
        decreases matrix@.len() - i
    {
        let mut j = 0;
        while j < matrix[i].len()
            invariant 
                0 <= i < matrix@.len(),
                0 <= j <= matrix@[i as int]@.len(),
                matrix@.len() > 0,
                forall|ii: int| #![auto] 0 <= ii < matrix@.len() ==> matrix@[ii]@.len() > 0
            decreases matrix@[i as int]@.len() - j
        {
            flat_values.push(matrix[i][j] / d);
            j += 1;
        }
        i += 1;
    }
    
    compute_min_ops(flat_values)
}
// </vc-code>


}

fn main() {}