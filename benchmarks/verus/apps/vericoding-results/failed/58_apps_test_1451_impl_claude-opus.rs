// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, numbers: Seq<int>) -> bool {
    n >= 1 && k >= 0 && numbers.len() == n && forall|i: int| 0 <= i < numbers.len() ==> numbers[i] > 0
}

spec fn count_lucky_digits(num: int) -> int
    decreases num when num >= 0
{
    if num <= 0 { 0 }
    else {
        let digit = num % 10;
        let rest = num / 10;
        let digit_count: int = if digit == 4 || digit == 7 { 1 } else { 0 };
        digit_count + count_lucky_digits(rest)
    }
}

spec fn count_valid_numbers(numbers: Seq<int>, k: int, up_to: int) -> int
    decreases up_to when up_to >= 0
{
    if up_to <= 0 { 0 }
    else {
        let prev_count = count_valid_numbers(numbers, k, up_to - 1);
        if count_lucky_digits(numbers[up_to - 1]) <= k { prev_count + 1 } else { prev_count }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary lemma and fixed count_lucky_digits_impl logic */
fn count_lucky_digits_impl(num: i8) -> (result: i8)
    ensures result as int == count_lucky_digits(num as int)
{
    if num <= 0 {
        proof {
            assert(count_lucky_digits(num as int) == 0);
        }
        return 0;
    }
    
    let mut n = num;
    let mut count: i8 = 0;
    
    proof {
        assert(count_lucky_digits(num as int) >= 0);
    }
    
    while n > 0
        invariant
            0 <= n <= num,
            0 <= count,
            count as int == count_lucky_digits(num as int) - count_lucky_digits(n as int),
        decreases n
    {
        let digit = n % 10;
        let old_n = n;
        n = n / 10;
        
        proof {
            assert(old_n as int == n as int * 10 + digit as int);
            assert(count_lucky_digits(old_n as int) == 
                   (if digit == 4 || digit == 7 { 1 } else { 0 }) + count_lucky_digits(n as int));
        }
        
        if digit == 4 || digit == 7 {
            count = count + 1;
        }
    }
    
    proof {
        assert(n == 0);
        assert(count_lucky_digits(0) == 0);
        assert(count as int == count_lucky_digits(num as int) - count_lucky_digits(0));
        assert(count as int == count_lucky_digits(num as int));
    }
    
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, numbers: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, numbers@.map(|i: int, x: i8| x as int))
    ensures 0 <= result as int <= n as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariant to properly track count_valid_numbers */
    let mut count: i8 = 0;
    let mut i: usize = 0;
    
    proof {
        assert(count_valid_numbers(numbers@.map(|j: int, x: i8| x as int), k as int, 0) == 0);
    }
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            numbers.len() == n as int,
            0 <= count as int <= i as int,
            count as int <= n as int,
            count as int == count_valid_numbers(numbers@.map(|j: int, x: i8| x as int), k as int, i as int),
        decreases numbers.len() - i
    {
        let num = numbers[i];
        let lucky_count = count_lucky_digits_impl(num);
        
        proof {
            let mapped_seq = numbers@.map(|j: int, x: i8| x as int);
            assert(mapped_seq[i as int] == num as int);
            assert(count_valid_numbers(mapped_seq, k as int, (i + 1) as int) ==
                   if count_lucky_digits(mapped_seq[i as int]) <= k as int {
                       count_valid_numbers(mapped_seq, k as int, i as int) + 1
                   } else {
                       count_valid_numbers(mapped_seq, k as int, i as int)
                   });
        }
        
        if lucky_count <= k {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == numbers.len());
        assert(count as int == count_valid_numbers(numbers@.map(|j: int, x: i8| x as int), k as int, n as int));
    }
    
    count
}
// </vc-code>


}

fn main() {}