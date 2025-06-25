// ATOM 
pub fn abs(x: int) -> int
{
    if x < 0 { -x } else { x }
}


// SPEC 

pub fn Testing_abs()
{
}



// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

// ATOM 


// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

pub fn max(a: int, b: int) -> int
{
    // Fill in an expression here.
    if a > b { a } else { b }
}

// SPEC 
pub fn Testing_max() {
}



// Exercise 6:

// SPEC 


// Exercise 6:

pub fn Abs(x: int) -> (y: int)
    ensures(abs(x) == y)
{
}



// Ghost
// ATOM 


// Ghost
pub fn Double(val: int) -> int
{
    2 * val
}


// SPEC 

pub fn TestDouble(val: int) -> (val2: int)
    ensures(val2 == Double(val))
{
}