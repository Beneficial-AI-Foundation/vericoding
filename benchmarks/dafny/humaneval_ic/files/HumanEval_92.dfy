This verification task involves implementing a function that checks if three real numbers satisfy two conditions: all three must be integers, and one of the numbers must equal the sum of the other two. The function should return true only if both conditions are met, false otherwise.

// ======= TASK =======
// Given three real numbers, return True if all three are integers and one number 
// equals the sum of the other two. Otherwise, return False.

// ======= SPEC REQUIREMENTS =======
predicate IsInteger(x: real)
{
    x == x.Floor as real
}

predicate AllIntegers(x: real, y: real, z: real)
{
    IsInteger(x) && IsInteger(y) && IsInteger(z)
}

predicate OneEqualsSumOfOtherTwo(x: real, y: real, z: real)
{
    x == y + z || y == x + z || z == x + y
}

predicate ValidResult(x: real, y: real, z: real, result: bool)
{
    result <==> (AllIntegers(x, y, z) && OneEqualsSumOfOtherTwo(x, y, z))
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method any_int(x: real, y: real, z: real) returns (result: bool)
    ensures ValidResult(x, y, z, result)
{
    var xIsInt := IsInteger(x);
    var yIsInt := IsInteger(y);
    var zIsInt := IsInteger(z);

    if xIsInt && yIsInt && zIsInt {
        result := OneEqualsSumOfOtherTwo(x, y, z);
    } else {
        result := false;
    }
}
