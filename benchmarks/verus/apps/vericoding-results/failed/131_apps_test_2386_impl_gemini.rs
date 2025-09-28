// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n && forall|i: int| 0 <= i < a.len() ==> a[i] >= 1
}

spec fn transform(a: Seq<int>) -> Seq<int> {
    Seq::new(a.len(), |i: int| a[i] - (i + 1))
}

spec fn sum_abs_diffs(a: Seq<int>, target: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        abs_int(a[0] - target) + sum_abs_diffs(a.subrange(1, a.len() as int), target)
    }
}

spec fn median_of(a: Seq<int>) -> int {
    let sorted = sorted_seq(a);
    if sorted.len() == 0 {
        0
    } else if sorted.len() % 2 == 1 {
        sorted[sorted.len() as int / 2]
    } else if sorted.len() == 2 {
        (sorted[0] + sorted[1]) / 2
    } else {
        (sorted[sorted.len() as int / 2 - 1] + sorted[sorted.len() as int / 2]) / 2
    }
}

spec fn sorted_seq(a: Seq<int>) -> Seq<int> {
    a
}

spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
fn abs_i64(x: i64) -> (res: i64)
    ensures
        res >= 0,
        res as int == abs_int(x as int),
{
    if x < 0 { -x } else { x }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map(|i: int, x: i8| x as int)),
    ensures 
        result >= 0,
        result as int == sum_abs_diffs(transform(a@.map(|i: int, x: i8| x as int)), median_of(transform(a@.map(|i: int, x: i8| x as int)))),
// </vc-spec>
// <vc-code>
{
    let n_nat = n as nat;
    let mut b: Vec<i8> = Vec::new_with_len(n_nat, 0);

    let ghost a_seq_int = a@.map(|_i: int, x: i8| x as int);
    let ghost b_spec_seq = transform(a_seq_int);

    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i <= n,
            n as int == a.len(),
            b.len() == n as nat,
            valid_input(n as int, a_seq_int),
            b_spec_seq == transform(a_seq_int),
            forall|j: int| 0 <= j < i as int ==> b@[j] as int == b_spec_seq[j],
    {
        let val_int = a[i as usize] as int - (i as int + 1);
        assert(-126 <= val_int <= 126);
        b.set(i as usize, val_int as i8);
        i = i + 1;
    }

    let ghost b_final_seq = b@.map(|_i: int, x: i8| x as int);
    assert(b_final_seq =~= b_spec_seq);

    let b_len = b.len();
    let median_val: int;
    if b_len % 2 == 1 {
        median_val = b[b_len / 2] as int;
    } else {
        median_val = (b[b_len/2 - 1] as int + b[b_len/2] as int) / 2;
    }

    assert(median_val == median_of(b_final_seq));

    let mut sum: i64 = 0;
    let mut j: i8 = 0;
    while j < n
        invariant
            0 <= j <= n,
            b.len() == n as nat,
            b_final_seq == b@.map(|_i: int, x: i8| x as int),
            median_val == median_of(b_final_seq),
            sum as int + sum_abs_diffs(b_final_seq.subrange(j as int, b_final_seq.len()), median_val)
                == sum_abs_diffs(b_final_seq, median_val),
    {
        let diff = b[j as usize] as i64 - median_val as i64;
        let abs_diff = abs_i64(diff);
        sum = sum + abs_diff;
        j = j + 1;
    }

    sum as i8
}
// </vc-code>


}

fn main() {}