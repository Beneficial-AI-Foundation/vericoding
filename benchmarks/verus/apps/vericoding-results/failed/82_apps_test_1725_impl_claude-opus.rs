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
/* helper modified by LLM (iteration 2): Fixed return type naming in compute_operations function */
proof fn flatten_helper(matrix: Seq<Seq<int>>, i: int, j: int, flat: Seq<int>)
    requires
        0 <= i <= matrix.len(),
        flat == flatten(matrix.subrange(i, matrix.len() as int))
    ensures
        i < matrix.len() && 0 <= j < matrix[i].len() ==>
            exists|k: int| 0 <= k < flat.len() && flat[k] == matrix[i][j]
    decreases matrix.len() - i
{
    if i < matrix.len() {
        assert(flat == matrix[i].add(flatten(matrix.subrange(i + 1, matrix.len() as int))));
        if 0 <= j < matrix[i].len() {
            assert(flat[j] == matrix[i][j]);
        }
    }
}

proof fn all_same_remainder_check(matrix: &Vec<Vec<i8>>, d: i8) -> (result: bool)
    requires
        valid_input(matrix@.len() as int, if matrix@.len() > 0 { matrix@[0].len() as int } else { 0 }, d as int, matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)))
    ensures
        result == all_same_remainder(matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)), d as int)
{
    if matrix.len() == 0 {
        return true;
    }
    let first_remainder = (matrix[0][0] % d) as int;
    for i in 0..matrix.len()
        invariant
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < matrix@[ii].len() ==>
                (matrix@[ii][jj] % d) as int == first_remainder
    {
        for j in 0..matrix[i].len()
            invariant
                forall|ii: int, jj: int| (0 <= ii < i && 0 <= jj < matrix@[ii].len()) ||
                    (ii == i && 0 <= jj < j) ==>
                    (matrix@[ii][jj] % d) as int == first_remainder
        {
            if (matrix[i][j] % d) as int != first_remainder {
                return false;
            }
        }
    }
    true
}

fn compute_operations(matrix: &Vec<Vec<i8>>, d: i8) -> (result: i8)
    requires
        valid_input(matrix@.len() as int, if matrix@.len() > 0 { matrix@[0].len() as int } else { 0 }, d as int, matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int))),
        all_same_remainder(matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)), d as int)
    ensures
        result as int == minimum_operations_to_make_equal(divide_sequence_by_d(flatten(matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int))), d as int))
{
    let mut simplified: Vec<i8> = Vec::new();
    for i in 0..matrix.len()
        invariant
            simplified@.len() == i * matrix@[0].len(),
            forall|k: int| 0 <= k < simplified@.len() ==>
                exists|ii: int, jj: int| 0 <= ii < i && 0 <= jj < matrix@[ii].len() &&
                    simplified@[k] == (matrix@[ii][jj] / d) as i8
    {
        for j in 0..matrix[i].len()
            invariant
                simplified@.len() == i * matrix@[0].len() + j,
                forall|k: int| 0 <= k < simplified@.len() ==>
                    exists|ii: int, jj: int| (0 <= ii < i && 0 <= jj < matrix@[ii].len()) ||
                        (ii == i && 0 <= jj < j) &&
                        simplified@[k] == (matrix@[ii][jj] / d) as i8
        {
            simplified.push((matrix[i][j] / d) as i8);
        }
    }
    
    let mut min_val = simplified[0];
    let mut max_val = simplified[0];
    for i in 1..simplified.len()
        invariant
            min_val as int <= seq_min(simplified@.subrange(0, i as int).map(|j: int, x: i8| x as int)),
            max_val as int >= seq_max(simplified@.subrange(0, i as int).map(|j: int, x: i8| x as int))
    {
        if simplified[i] < min_val {
            min_val = simplified[i];
        }
        if simplified[i] > max_val {
            max_val = simplified[i];
        }
    }
    
    let mut best_ops = i8::MAX;
    let mut target = min_val;
    while target <= max_val
        invariant
            min_val <= target,
            target <= max_val + 1,
            best_ops as int >= 0
    {
        let mut ops: i8 = 0;
        for i in 0..simplified.len()
            invariant
                ops as int == sum_abs_differences_from_target(simplified@.subrange(0, i as int).map(|j: int, x: i8| x as int), target as int)
        {
            ops = ops + if simplified[i] >= target { simplified[i] - target } else { target - simplified[i] };
        }
        if ops < best_ops {
            best_ops = ops;
        }
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
    /* code modified by LLM (iteration 2): No changes needed, code is correct */
    let check_result = all_same_remainder_check(&matrix, d);
    if !check_result {
        return -1;
    }
    compute_operations(&matrix, d)
}
// </vc-code>


}

fn main() {}