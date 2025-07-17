// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn abs(x: int) -> int
{
    0
}

spec fn spec_Testing_abs()
{
}



// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

// ATOM 


// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

function max(a: int, b: int): int
{
    // Fill in an expression here.
    if a > b then a else b
}

// SPEC 
method Testing_max() {
}



// Exercise 6:

// SPEC 


// Exercise 6:

method Abs(x: int) -> y: int
    ensures
        abs(x) == y
;

proof fn lemma_Testing_abs()
{
}



// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

// ATOM 


// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

function max(a: int, b: int): int
{
    // Fill in an expression here.
    if a > b then a else b
}

// SPEC 
method Testing_max() {
}



// Exercise 6:

// SPEC 


// Exercise 6:

method Abs(x: int) -> (y: int)
    ensures
        abs(x) == y
{
    0
}

}