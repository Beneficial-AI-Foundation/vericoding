//IMPL abs
function abs(x: int): int
{
    if x >= 0 then x else -x
}

//IMPL Testing_abs
method Testing_abs()
{
    assert abs(5) == 5;
    assert abs(-3) == 3;
    assert abs(0) == 0;
}

// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

//IMPL max
function max(a: int, b: int): int
{
    if a >= b then a else b
}

//IMPL Testing_max
method Testing_max() {
    assert max(5, 3) == 5;
    assert max(2, 8) == 8;
    assert max(4, 4) == 4;
    assert max(-2, -5) == -2;
}

// Exercise 6:

//IMPL Abs
method Abs(x: int) returns (result: int)
    ensures result >= 0
    ensures result == x || result == -x
    ensures x >= 0 ==> result == x
    ensures x < 0 ==> result == -x
{
    if x >= 0 {
        result := x;
    } else {
        result := -x;
    }
}

// Ghost
//IMPL Double
function Double(x: int): int
{
    x * 2
}

//IMPL TestDouble
method TestDouble()
{
    assert Double(5) == 10;
    assert Double(0) == 0;
    assert Double(-3) == -6;
}