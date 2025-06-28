verus! {
use builtin::*;
use builtin_macros::*;

// Example of correct ensures syntax - please provide your actual functions
fn example_function(n: i32) -> (result: i32)
    ensures result == n + 1
{
    n + 1
}

// Additional helper functions to demonstrate verified Verus code

// A simple arithmetic function
fn add_two_numbers(a: i32, b: i32) -> (result: i32)
    ensures result == a + b
{
    a + b
}

// A function with requires clause
fn safe_divide(dividend: i32, divisor: i32) -> (result: i32)
    requires divisor != 0
    ensures result == dividend / divisor
{
    dividend / divisor
}

// A function working with natural numbers
fn increment_nat(n: nat) -> (result: nat)
    ensures result == n + 1
{
    n + 1
}

// A spec function for use in other specifications
spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// A function using the spec function
fn double_number(n: i32) -> (result: i32)
    ensures is_even(result as int)
    ensures result == 2 * n
{
    2 * n
}

// A function with a loop and invariant
fn sum_to_n(n: u32) -> (result: u32)
    ensures result == n * (n + 1) / 2
{
    let mut sum = 0u32;
    let mut i = 0u32;
    
    while i <= n
        invariant sum == i * (i - 1) / 2
        invariant i <= n + 1
    {
        sum = sum + i;
        i = i + 1;
    }
    
    sum
}

} // verus!