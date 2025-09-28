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
/* helper modified by LLM (iteration 5): convert runtime matrix Vec<Vec<i8>> to spec Seq<Seq<int>> */
spec fn matrix_to_seq(matrix: Vec<Vec<i8>>) -> Seq<Seq<int>> {
    matrix@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int))
}

/* helper modified by LLM (iteration 5): flatten matrix into a spec seq */
spec fn flattened_view(matrix: Vec<Vec<i8>>) -> Seq<int> {
    flatten(matrix_to_seq(matrix))
}

/* helper modified by LLM (iteration 5): divide elements by d in spec */
spec fn simplified_view(matrix: Vec<Vec<i8>>, d: i8) -> Seq<int> {
    divide_sequence_by_d(flattened_view(matrix), d as int)
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
    /* code modified by LLM (iteration 5): check remainders, build simplified vector, compute minimal ops */
    let n_int = n as int;
    let m_int = m as int;
    let d_int = d as int;

    // check all remainders equal to first element's remainder
    let first_r: i8 = matrix[0usize][0usize] % d;
    let mut i: int = 0;
    while i < n_int
        invariant
            0 <= i,
            i <= n_int,
        decreases n_int - i
    {
        let mut j: int = 0;
        while j < m_int
            invariant
                0 <= j,
                j <= m_int,
            decreases m_int - j
        {
            if matrix[i as usize][j as usize] % d != first_r {
                return -1;
            }
            j += 1;
        }
        i += 1;
    }

    // build simplified vector (values divided by d)
    let mut simplified: Vec<i64> = Vec::new();
    let mut ii: int = 0;
    while ii < n_int
        invariant
            0 <= ii,
            ii <= n_int,
            simplified.len() as int == ii * m_int,
        decreases n_int - ii
    {
        let mut jj: int = 0;
        while jj < m_int
            invariant
                0 <= jj,
                jj <= m_int,
                simplified.len() as int == ii * m_int + jj,
            decreases m_int - jj
        {
            simplified.push((matrix[ii as usize][jj as usize] / d) as i64);
            jj += 1;
        }
        ii += 1;
    }

    // find min and max in simplified
    let mut minv: i64 = simplified[0usize];
    let mut maxv: i64 = simplified[0usize];
    let mut k: int = 1;
    while k < simplified.len() as int
        invariant
            0 <= k,
            k <= simplified.len() as int,
        decreases simplified.len() as int - k
    {
        let val = simplified[k as usize];
        if val < minv { minv = val; }
        if val > maxv { maxv = val; }
        k += 1;
    }

    // brute-force try every target between minv and maxv
    let mut best: i64 = 9223372036854775807i64;
    let mut target: i64 = minv;
    while target <= maxv
        invariant
            minv <= target,
            target <= maxv + 1,
            best >= 0,
        decreases (maxv - target) + 1
    {
        let mut sum: i64 = 0;
        let mut p: int = 0;
        while p < simplified.len() as int
            invariant
                0 <= p,
                p <= simplified.len() as int,
                sum >= 0,
            decreases simplified.len() as int - p
        {
            let v = simplified[p as usize];
            if v >= target { sum += v - target; } else { sum += target - v; }
            p += 1;
        }
        if sum < best { best = sum; }
        target += 1;
    }

    best as i8
}
// </vc-code>


}

fn main() {}