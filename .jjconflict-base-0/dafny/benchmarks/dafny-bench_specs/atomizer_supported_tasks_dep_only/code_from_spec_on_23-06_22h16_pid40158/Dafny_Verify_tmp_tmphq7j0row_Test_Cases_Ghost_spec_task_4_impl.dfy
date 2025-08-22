//ATOM Average
function Average(a: int, b: int): int
{
    (a + b) / 2
}

//ATOM Triple
function Triple(x: int): int
{
    3 * x
}

//ATOM Triple1
function Triple1(x: int): int
{
    x + x + x
}

//ATOM DoubleQuadruple
function DoubleQuadruple(x: int): int
{
    8 * x
}

//ATOM F
function F(x: int): int
{
    x + 1
}

//ATOM M
method M(x: int) returns (y: int)
{
    y := x * 2;
}

//ATOM Caller
method Caller() returns (result: int)
{
    result := 42;
}

//IMPL MyMethod
method MyMethod(x: int) returns (y: int)
    requires 10 <= x
    ensures 25 <= y
{
    y := 25;
}