// ATOM 
function abs(x: int): int
{
    if x < 0 then -x else x
}


//ATOM_PLACEHOLDER_Testing_abs


// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

//ATOM_PLACEHOLDER_max
//ATOM_PLACEHOLDER_Testing_max


// Exercise 6:

//IMPL Abs
method Abs(x: int) returns (y: int)
    ensures abs(x) == y
{
    if x < 0 {
        y := -x;
    } else {
        y := x;
    }
}



// Ghost
//ATOM_PLACEHOLDER_Double

//ATOM_PLACEHOLDER_TestDouble