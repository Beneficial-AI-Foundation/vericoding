// ATOM 
function abs(x: int): int
{
    if x < 0 then -x else x
}

//IMPL 
method Testing_abs()
{
    assert abs(5) == 5;
    assert abs(-3) == 3;
    assert abs(0) == 0;
}

// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

//ATOM max
function max(a: int, b: int): int
{
    if a >= b then a else b
}

//ATOM Testing_max
method Testing_max()
{
    assert max(5, 3) == 5;
    assert max(2, 7) == 7;
    assert max(4, 4) == 4;
    assert max(-1, -5) == -1;
}

// Exercise 6:

//ATOM Abs
function Abs(x: int): int
{
    if x < 0 then -x else x
}

// Ghost
//ATOM Double
ghost function Double(x: int): int
{
    x * 2
}

//ATOM TestDouble
method TestDouble()
{
    assert Double(5) == 10;
    assert Double(-3) == -6;
    assert Double(0) == 0;
}