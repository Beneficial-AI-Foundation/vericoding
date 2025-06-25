// ATOM 
pub fn Average(a: int, b: int) -> int 
{
    (a + b) / 2
}


// ATOM 

pub fn Triple(x: int) -> (r: int)
    ensures(r == 3 * x)
{
    Average(2 * x, 4 * x)
}


// SPEC 

pub fn Triple1(x: int) -> (r: int)
    ensures(r == 3 * x)
{
}


// ATOM 

pub fn DoubleQuadruple(x: int) -> (a: int, b: int)
    ensures(a == 2 * x && b == 4 * x)
{
    let a = 2 * x;
    let b = 2 * a;
    (a, b)
}


// ATOM 

pub fn F() -> int {
    29
}


// SPEC 

pub fn M() -> (r: int) 
    ensures(r == 29)
{
}


// SPEC 

pub fn Caller() {
}


// SPEC 

pub fn MyMethod(x: int) -> (y: int)
    requires(10 <= x)
    ensures(25 <= y)
{
}