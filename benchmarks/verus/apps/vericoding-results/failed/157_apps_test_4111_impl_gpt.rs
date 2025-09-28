// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    n >= 1 && arr.len() == n && forall|i: int| 0 <= i < n ==> arr[i] >= 1
}

spec fn sum_even_indices(arr: Seq<int>, start: int) -> int
    decreases arr.len() - start when 0 <= start <= arr.len()
{
    if start == arr.len() {
        0
    } else {
        let contribution = if start % 2 == 0 { arr[start] } else { 0 };
        contribution + sum_even_indices(arr, start + 1)
    }
}

spec fn sum_odd_indices(arr: Seq<int>, start: int) -> int
    decreases arr.len() - start when 0 <= start <= arr.len()
{
    if start == arr.len() {
        0
    } else {
        let contribution = if start % 2 == 1 { arr[start] } else { 0 };
        contribution + sum_odd_indices(arr, start + 1)
    }
}

spec fn count_balanced_removals(arr: Seq<int>) -> int {
    let n = arr.len();
    if n == 0 {
        0
    } else {
        count_helper(arr, 0, sum_even_indices(arr, 0), sum_odd_indices(arr, 0), 0, 0)
    }
}

spec fn count_helper(arr: Seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int) -> int
    decreases arr.len() - i when 0 <= i <= arr.len()
{
    if i == arr.len() {
        0
    } else {
        let contribution: int = 
            if i % 2 == 0 {
                let val1 = temp1 + count2 - temp2;
                let val2 = temp2 + count1 - temp1 - arr[i];
                if val1 == val2 { 1 } else { 0 }
            } else {
                let val1 = temp1 + count2 - temp2 - arr[i];
                let val2 = temp2 + count1 - temp1;
                if val1 == val2 { 1 } else { 0 }
            };
        let new_temp1 = if i % 2 == 0 { temp1 + arr[i] } else { temp1 };
        let new_temp2 = if i % 2 == 1 { temp2 + arr[i] } else { temp2 };
        contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): unfolding lemmas and map-length lemma */
proof fn lemma_sum_even_unfold(arr: Seq<int>, i: int)
    requires
        0 <= i,
        i < arr.len(),
    ensures
        sum_even_indices(arr, i) == (if i % 2 == 0 { arr[i] } else { 0 }) + sum_even_indices(arr, i + 1),
{
    assert(sum_even_indices(arr, i) == (
        if i == arr.len() {
            0
        } else {
            let contribution = if i % 2 == 0 { arr[i] } else { 0 };
            contribution + sum_even_indices(arr, i + 1)
        }
    ));
}

/* helper modified by LLM (iteration 3): unfolding lemma for sum_odd_indices */
proof fn lemma_sum_odd_unfold(arr: Seq<int>, i: int)
    requires
        0 <= i,
        i < arr.len(),
    ensures
        sum_odd_indices(arr, i) == (if i % 2 == 1 { arr[i] } else { 0 }) + sum_odd_indices(arr, i + 1),
{
    assert(sum_odd_indices(arr, i) == (
        if i == arr.len() {
            0
        } else {
            let contribution = if i % 2 == 1 { arr[i] } else { 0 };
            contribution + sum_odd_indices(arr, i + 1)
        }
    ));
}

/* helper modified by LLM (iteration 3): unfolding lemma for count_helper */
proof fn lemma_count_helper_unfold(arr: Seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int)
    requires
        0 <= i,
        i < arr.len(),
    ensures
        count_helper(arr, i, count1, count2, temp1, temp2) == {
            let contribution: int = if i % 2 == 0 {
                let val1 = temp1 + count2 - temp2;
                let val2 = temp2 + count1 - temp1 - arr[i];
                if val1 == val2 { 1 } else { 0 }
            } else {
                let val1 = temp1 + count2 - temp2 - arr[i];
                let val2 = temp2 + count1 - temp1;
                if val1 == val2 { 1 } else { 0 }
            };
            let new_temp1 = if i % 2 == 0 { temp1 + arr[i] } else { temp1 };
            let new_temp2 = if i % 2 == 1 { temp2 + arr[i] } else { temp2 };
            contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2)
        },
{
    assert(count_helper(arr, i, count1, count2, temp1, temp2) ==
        if i == arr.len() {
            0
        } else {
            let contribution: int = if i % 2 == 0 {
                let val1 = temp1 + count2 - temp2;
                let val2 = temp2 + count1 - temp1 - arr[i];
                if val1 == val2 { 1 } else { 0 }
            } else {
                let val1 = temp1 + count2 - temp2 - arr[i];
                let val2 = temp2 + count1 - temp1;
                if val1 == val2 { 1 } else { 0 }
            };
            let new_temp1 = if i % 2 == 0 { temp1 + arr[i] } else { temp1 };
            let new_temp2 = if i % 2 == 1 { temp2 + arr[i] } else { temp2 };
            contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2)
        }
    );
}

/* helper modified by LLM (iteration 3): map length preservation for i8->int */
proof fn lemma_map_len_i8_to_int(a: Seq<i8>)
    ensures
        a.map(|i: int, x: i8| x as int).len() == a.len(),
{
    assert(a.map(|i: int, x: i8| x as int).len() == a.len());
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, arr@.map(|i: int, x: i8| x as int)),
    ensures 
        0 <= result as int <= n as int,
        result as int == count_balanced_removals(arr@.map(|i: int, x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): removed problematic assert inside proof blocks; kept unfolding lemmas; two-pass computation */
    let ghost s: Seq<int> = arr@.map(|i: int, x: i8| x as int);
    proof {
        lemma_map_len_i8_to_int(arr@);
        assert(s.len() == arr.len() as int);
    }

    // First pass: compute total sums at even and odd indices
    let mut i: usize = 0;
    let mut even_sum: i32 = 0;
    let mut odd_sum: i32 = 0;
    while i < arr.len()
        invariant
            0 <= i as int <= s.len(),
            even_sum as int == sum_even_indices(s, 0) - sum_even_indices(s, i as int),
            odd_sum as int == sum_odd_indices(s, 0) - sum_odd_indices(s, i as int),
        decreases s.len() - i as int
    {
        proof {
            lemma_sum_even_unfold(s, i as int);
            lemma_sum_odd_unfold(s, i as int);
        }
        let ai_i32: i32 = arr[i] as i32;
        if i % 2 == 0 {
            even_sum = even_sum + ai_i32;
        } else {
            odd_sum = odd_sum + ai_i32;
        }
        i = i + 1usize;
    }

    proof {
        assert(sum_even_indices(s, s.len()) == 0);
        assert(sum_odd_indices(s, s.len()) == 0);
        assert(even_sum as int == sum_even_indices(s, 0));
        assert(odd_sum as int == sum_odd_indices(s, 0));
    }

    let c1: i32 = even_sum;
    let c2: i32 = odd_sum;

    // Second pass: count balanced removals
    let mut idx: usize = 0;
    let mut t1: i32 = 0;
    let mut t2: i32 = 0;
    let mut pc: i32 = 0;

    while idx < arr.len()
        invariant
            0 <= idx as int <= s.len(),
            0 <= pc as int,
            pc as int <= idx as int,
            pc as int + count_helper(s, idx as int, c1 as int, c2 as int, t1 as int, t2 as int)
                == count_helper(s, 0, c1 as int, c2 as int, 0, 0),
        decreases s.len() - idx as int
    {
        proof {
            lemma_count_helper_unfold(s, idx as int, c1 as int, c2 as int, t1 as int, t2 as int);
        }
        let ai_i32: i32 = arr[idx] as i32;
        if idx % 2 == 0 {
            let val1_i32: i32 = t1 + c2 - t2;
            let val2_i32: i32 = t2 + c1 - t1 - ai_i32;
            let contrib: i32 = if val1_i32 == val2_i32 { 1 } else { 0 };
            pc = pc + contrib;
            t1 = t1 + ai_i32;
        } else {
            let val1_i32: i32 = t1 + c2 - t2 - ai_i32;
            let val2_i32: i32 = t2 + c1 - t1;
            let contrib: i32 = if val1_i32 == val2_i32 { 1 } else { 0 };
            pc = pc + contrib;
            t2 = t2 + ai_i32;
        }
        idx = idx + 1usize;
    }

    // Tie result to spec
    proof {
        assert(count_helper(s, s.len(), c1 as int, c2 as int, t1 as int, t2 as int) == 0);
        assert(pc as int == count_helper(s, 0, c1 as int, c2 as int, 0, 0));
        assert(count_balanced_removals(s) == count_helper(s, 0, sum_even_indices(s, 0), sum_odd_indices(s, 0), 0, 0));
        assert(c1 as int == sum_even_indices(s, 0));
        assert(c2 as int == sum_odd_indices(s, 0));
        assert(pc as int == count_balanced_removals(s));
    }

    // Casting safety (may be strengthened by caller constraints)
    let result: i8 = pc as i8;
    result
}
// </vc-code>


}

fn main() {}