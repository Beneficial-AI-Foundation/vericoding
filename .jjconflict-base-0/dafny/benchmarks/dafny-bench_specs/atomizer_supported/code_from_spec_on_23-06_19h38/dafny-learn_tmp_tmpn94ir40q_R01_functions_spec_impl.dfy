// ATOM 
function abs(x: int): int
{
    if x < 0 then -x else x
}

//IMPL Testing_abs
method Testing_abs()
{
    assert abs(5) == 5;
    assert abs(-3) == 3;
    assert abs(0) == 0;
}

// ATOM 
function max(a: int, b: int): int
{
    // Fill in an expression here.
    if a > b then a else b
}

//IMPL Testing_max
method Testing_max() {
    assert max(5, 3) == 5;
    assert max(2, 7) == 7;
    assert max(4, 4) == 4;
}

//IMPL Abs
method Abs(x: int) returns (y: int)
    ensures abs(x) == y
{
    y := abs(x);
}

// ATOM 
ghost function Double(val:int) : int
{
    2 * val
}

//IMPL TestDouble
method TestDouble(val: int) returns (val2:int)
    ensures val2 == Double(val)
{
    /* code modified by LLM (iteration 1): replaced ghost function call with executable computation */
    val2 := 2 * val;
}