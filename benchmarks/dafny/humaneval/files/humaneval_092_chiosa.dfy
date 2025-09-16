// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method any_int(x: real, y: real, z: real) returns (result: bool)
    ensures ValidResult(x, y, z, result)
// </vc-spec>
// <vc-code>
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
// </vc-code>
