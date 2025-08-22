// ATOM 
function Average(a: int, b: int): int 
{
    (a + b) / 2
}


// ATOM 

ghost method Triple(x: int) returns (r: int)
    ensures r == 3 * x
{
    r := Average(2 * x, 4 * x);
}


// SPEC 

method Triple1(x: int) returns (r: int)
    ensures r == 3 * x
{
}


// ATOM 

ghost method DoubleQuadruple(x: int) returns (a: int, b: int)
    ensures a == 2 * x && b == 4 * x
{
    a := 2 * x;
    b := 2 * a;
}


// ATOM 

function F(): int {
29
}


// SPEC 

method M() returns (r: int) 
ensures r == 29
{
}


// SPEC 

method Caller() {
}


// SPEC 

method MyMethod(x: int) returns (y: int)
    requires 10 <= x
    ensures 25 <= y
{
}


