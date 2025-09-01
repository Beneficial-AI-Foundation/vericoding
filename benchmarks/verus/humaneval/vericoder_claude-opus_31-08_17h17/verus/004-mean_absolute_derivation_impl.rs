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
proof fn lemma_sum_single(x: int)
    ensures sum(seq![x]) == x
{
    reveal(sum);
    assert(seq![x].len() == 1);
    assert(seq![x][0] == x);
}

proof fn lemma_sum_push(s: Seq<int>, x: int)
    ensures sum(s.push(x)) == sum(s) + x
{
    reveal(sum);
    s.lemma_fold_left_alt(0, |acc: int, y| acc + y);
}

proof fn lemma_map_len<A, B>(s: Seq<A>, f: spec_fn(int, A) -> B)
    ensures s.map(f).len() == s.len()
{
}

proof fn lemma_sum_map_bounds(s: Seq<int>, mean_val: int)
    ensures 
        s.len() > 0 ==> sum(s.map(|_index, n: int| abs(n - mean_val))) >= 0
{
    if s.len() > 0 {
        let mapped = s.map(|_index, n: int| abs(n - mean_val));
        assert forall|i: int| 0 <= i < mapped.len() implies mapped[i] >= 0 by {
            assert(abs(s[i] - mean_val) >= 0);
        }
        lemma_sum_non_negative(mapped);
    }
}

proof fn lemma_sum_non_negative(s: Seq<int>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
    ensures
        sum(s) >= 0,
    decreases s.len(),
{
    reveal(sum);
    if s.len() == 0 {
        assert(sum(s) == 0);
    } else {
        lemma_sum_push(s.drop_last(), s.last());
        assert(s.drop_last().len() == s.len() - 1);
        assert forall|i: int| 0 <= i < s.drop_last().len() implies s.drop_last()[i] >= 0 by {
            assert(s.drop_last()[i] == s[i]);
        }
        lemma_sum_non_negative(s.drop_last());
    }
}

proof fn lemma_sum_bounds(numbers: Seq<i32>)
    requires numbers.len() > 0,
    ensures 
        i32::MIN as int * numbers.len() as int <= sum(numbers@.map(|_index, x: i32| x as int)),
        sum(numbers@.map(|_index, x: i32| x as int)) <= i32::MAX as int * numbers.len() as int,
    decreases numbers.len(),
{
    reveal(sum);
    if numbers.len() == 1 {
        lemma_sum_single(numbers[0] as int);
        assert(sum(numbers@.map(|_index, x: i32| x as int)) == numbers[0] as int);
    } else {
        let init = numbers.drop_last();
        let last = numbers.last();
        lemma_sum_push(init@.map(|_index, x: i32| x as int), last as int);
        lemma_sum_bounds(init);
    }
}

fn divide_i32_by_usize(x: i32, d: usize) -> (result: (i32, usize))
    requires
        d > 0,
        d <= i32::MAX as usize,
        x >= 0,
        x as int / d as int <= i32::MAX,
    ensures
        expr_inner_divide_i32_by_usize(result, x, d),
{
    assert(d as i32 != 0);
    let q = x / (d as i32);
    let r = x % (d as i32);
    assert(0 <= r < d as i32);
    assert(r as usize <= usize::MAX);
    assert(x as int == q as int * d as int + r as int) by {
        lemma_fundamental_div_mod(x as int, d as int);
    }
    (q, r as usize)
}
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
    let n = numbers.len();
    assert(n <= i32::MAX as usize);  // Reasonable assumption for array size
    
    // Calculate sum
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    proof {
        lemma_sum_bounds(numbers@);
    }
    
    while i < n
        invariant
            i <= n,
            n == numbers@.len(),
            n <= i32::MAX as usize,
            total == sum(numbers@.take(i as int).map(|_index, x: i32| x as int)),
            i32::MIN as int * n as int <= sum(numbers@.map(|_index, x: i32| x as int)),
            sum(numbers@.map(|_index, x: i32| x as int)) <= i32::MAX as int * n as int,
            i32::MIN <= total <= i32::MAX,
        decreases n - i,
    {
        assert(i32::MIN <= total + numbers[i] <= i32::MAX) by {
            assert(numbers@.take((i + 1) as int) =~= numbers@.take(i as int).push(numbers@[i as int]));
            reveal(sum);
        }
        
        total = total + numbers[i];
        
        proof {
            assert(numbers@.take((i + 1) as int) =~= numbers@.take(i as int).push(numbers@[i as int]));
            lemma_sum_push(numbers@.take(i as int).map(|_index, x: i32| x as int), numbers@[i as int] as int);
        }
        
        i = i + 1;
    }
    
    assert(numbers@.take(n as int) =~= numbers@);
    assert(n as i32 != 0);
    let mean_val = total / (n as i32);
    
    proof {
        assert(mean_val == sum(numbers@.map(|_index, x: i32| x as int)) / (n as int)) by {
            reveal(sum);
        }
    }
    
    // Calculate sum of absolute deviations
    let mut dev_sum: i32 = 0;
    i = 0;
    
    while i < n
        invariant
            i <= n,
            n == numbers@.len(),
            n <= i32::MAX as usize,
            mean_val == sum(numbers@.map(|_index, x: i32| x as int)) / (n as int),
            dev_sum >= 0,
            dev_sum <= i32::MAX,
            dev_sum == sum(numbers@.take(i as int).map(|_index, x: i32| abs(x as int - mean_val as int))),
        decreases n - i,
    {
        let diff = if numbers[i] >= mean_val {
            assert(numbers[i] - mean_val >= 0);
            assert(numbers[i] - mean_val <= i32::MAX);
            numbers[i] - mean_val
        } else {
            assert(mean_val - numbers[i] >= 0);
            assert(mean_val - numbers[i] <= i32::MAX);
            mean_val - numbers[i]
        };
        
        assert(diff >= 0);
        assert(diff == abs(numbers@[i as int] as int - mean_val as int));
        assert(dev_sum + diff <= i32::MAX);
        
        dev_sum = dev_sum + diff;
        
        proof {
            assert(numbers@.take((i + 1) as int) =~= numbers@.take(i as int).push(numbers@[i as int]));
            lemma_sum_push(
                numbers@.take(i as int).map(|_index, x: i32| abs(x as int - mean_val as int)),
                abs(numbers@[i as int] as int - mean_val as int)
            );
        }
        
        i = i + 1;
    }
    
    assert(numbers@.take(n as int) =~= numbers@);
    assert(dev_sum == sum(numbers@.map(|_index, x: i32| abs(x as int - mean_val as int))));
    
    let (result_i32, _) = divide_i32_by_usize(dev_sum, n);
    
    proof {
        assert(mean_val == mean(numbers@.map(|_index, n: i32| n as int)));
        assert(result_i32 == spec_mean_absolute_deviation(numbers@.map(|_index, n: i32| n as int)));
    }
    
    assert(result_i32 >= 0);
    result_i32 as u32
}
// </vc-code>

fn main() {}
}