//ATOM_PLACEHOLDER_abs

//ATOM_PLACEHOLDER_Testing_abs


// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

//ATOM_PLACEHOLDER_max
//ATOM_PLACEHOLDER_Testing_max


// Exercise 6:

//ATOM_PLACEHOLDER_Abs


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


