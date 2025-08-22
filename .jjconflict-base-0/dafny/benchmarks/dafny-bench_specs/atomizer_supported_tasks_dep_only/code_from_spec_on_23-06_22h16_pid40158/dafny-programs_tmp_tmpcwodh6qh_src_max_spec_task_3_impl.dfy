//ATOM Max
function Max(a: int, b: int): int
{
    if a >= b then a else b
}

//ATOM MaxTest
method MaxTest(a: int, b: int) returns (result: int)
    ensures result == Max(a, b)
    ensures result >= a && result >= b
{
    if a >= b {
        result := a;
    } else {
        result := b;
    }
}

//ATOM max
function max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else Max(s[0], max(s[1..]))
}

//IMPL maxTest
method maxTest() {
    // Test the Max function with some values
    var result1 := MaxTest(5, 3);
    assert result1 == 5;
    
    var result2 := MaxTest(2, 8);
    assert result2 == 8;
    
    var result3 := MaxTest(4, 4);
    assert result3 == 4;
    
    // Test with negative numbers
    var result4 := MaxTest(-1, -5);
    assert result4 == -1;
}