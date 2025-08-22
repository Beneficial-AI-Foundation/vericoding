// ATOM 
function abs(x: int): int
{
    if x < 0 then -x else x
}


// SPEC 

method Testing_abs()
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

method Abs(x: int) returns (y: int)
    ensures abs(x) == y
{
}



// Ghost
// ATOM 


// Ghost
ghost function Double(val:int) : int
{
    2 * val
}


// SPEC 

method TestDouble(val: int) returns (val2:int)
    ensures val2 == Double(val)
{
}


