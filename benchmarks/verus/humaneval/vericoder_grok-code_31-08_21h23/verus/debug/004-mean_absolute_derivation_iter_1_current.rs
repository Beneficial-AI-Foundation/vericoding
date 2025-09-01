use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_div_is_ordered_by_denominator, lemma_div_multiples_vanish,
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
};
use vstd::arithmetic::mul::{
    lemma_mul_inequality, lemma_mul_is_distributive_add, lemma_mul_is_distributive_add_other_way,
    lemma_mul_unary_negation,
};
use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<int>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}
// pure-end
// pure-end

spec fn mean(values: Seq<int>) -> (result:int)
    recommends
        values.len() > 0,
{
    sum(values) / (values.len() as int)
}
// pure-end
// pure-end

spec fn abs(n: int) -> (result:int) {
    if n >= 0 {
        n
    } else {
        -n
    }
}
// pure-end
// pure-end

spec fn spec_mean_absolute_deviation(numbers: Seq<int>) -> (result:int)
    recommends
        numbers.len() > 0,
{
    let avg = mean(numbers);
    sum(numbers.map(|_index, n: int| abs(n - avg))) / (numbers.len() as int)
}
// pure-end
// pure-end

spec fn if_inner_lemma_how_to_add_then_divide(x : int, y : int, d : int) -> (result: bool) {
    if (x % d) + (y % d) >= d {
        &&& (x + y) / d == (x / d) + (y / d) + 1
        &&& (x + y) % d == (x % d) + (y % d) - d
    } else {
        &&& (x + y) / d == (x / d) + (y / d)
        &&& (x + y) % d == (x % d) + (y % d)
    }
}
// pure-end
// pure-end


spec fn expr_inner_divide_i32_by_u32(qr : (i32, u32), x: i32, d: u32) -> (result:bool) {
    let (q, r) = qr;
    q == x as int / d as int && r == x as int % d as int
}
// pure-end
spec fn expr_inner_divide_i32_by_usize(qr : (i32, usize), x: i32, d: usize) -> (result:bool) {
    let (q, r) = qr;
    q == x as int / d as int && r == x as int % d as int
}
// pure-end

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mean_absolute_deviation(numbers: &[i32]) -> (result: u32)
    // pre-conditions-start
    requires
        numbers.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == spec_mean_absolute_deviation(numbers@.map(|_index, n: i32| n as int)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = numbers.len() as int;
    let spec_numbers = numbers@.map(|_, n: i32| n as int);
    let total_sum_spec = sum(spec_numbers);
    let average = total_sum_spec / len;
    let result_spec = spec_mean_absolute_deviation(spec_numbers);
    let mut total_sum_i64 = 0i64;
    let mut index = 0usize;
    while index < numbers.len() 
        invariant
            0 <= index <= numbers.len(),
            total_sum_i64 == sum(spec_numbers.take(index as int)),
    {
        proof {
            if index != 0 {
                assert(spec_numbers.take(index as int) == spec_numbers.take((index - 1) as int) + seq![spec_numbers[index - 1]]);
                assert(sum(spec_numbers.take(index as int)) == sum(spec_numbers.take((index - 1) as int)) + spec_numbers[index - 1]);
            }
        }
        total_sum_i64 = total_sum_i64 + (numbers[index] as i64);
        index = index + 1;
    }
    proof {
        assert(total_sum_i64 == total_sum_spec);
    }
    let len_i64 = numbers.len() as i64;
    let average_i64 = if len_i64 != 0 { total_sum_i64 / len_i64 } else { 0 };
    proof {
        lemma_fundamental_div_mod(total_sum_spec, len, total_sum_spec / len, total_sum_spec % len);
        lemma_fundamental_div_mod_converse(total_sum_spec, len, total_sum_spec / len, total_sum_spec % len);
        assert(average_i64 == average);
    }
    let mut sum_abs_i64 = 0i64;
    index = 0;
    while index < numbers.len() 
        invariant
            0 <= index <= numbers.len(),
            sum_abs_i64 == sum(spec_numbers.take(index as int).map(|_, n: int| abs(n - average))),
    {
        proof {
            if index != 0 {
                assert(spec_numbers.take(index as int) == spec_numbers.take((index - 1) as int) + seq![spec_numbers[index - 1]]);
                assert(sum(spec_numbers.take(index as int).map(|_, n: int| abs(n - average))) == 
                    sum(spec_numbers.take((index - 1) as int).map(|_, n: int| abs(n - average))) + abs(spec_numbers[index - 1] - average));
            }
        }
        let n.i32 = numbers[index];
        let n_int = spec_numbers[index as int];
        let n_i64 = n_i32 as i64;
        let diff = if average_i64 <= n_i64 { n_i64 - average_i64 } else { average_i64 - n_i64 };
        proof {
            assert(abs(n_int - average) == diff);
        }
        sum_abs_i64 = sum_abs_i64 + diff;
        index = index + 1;
    }
    proof {
        assert(sum_abs_i64 == sum(spec_numbers.map(|_, n: int| abs(n - average))));
        lemma_fundamental_div_mod(sum_abs_i64 as int, len, (sum_abs_i64 as int) / len, (sum_abs_i64 as int) % len);
        assert((sum_abs_i64 as int) / len == result_spec);
    }
    let numerator_u64 = sum_abs_i64 as u64;
    let temp_result = (numerator_u64 / (numbers.len() as u64)) as u32;
    assert(temp_result as int == result_spec);
    temp_result
}
// </vc-code>

fn main() {}
}