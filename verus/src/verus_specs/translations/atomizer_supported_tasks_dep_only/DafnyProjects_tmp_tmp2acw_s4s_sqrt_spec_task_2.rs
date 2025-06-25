// SPEC 

pub fn sqrt(x: real) -> (r: real)
    requires x >= 0.0
    ensures r * r == x && r >= 0.0
{
}

pub fn testSqrt() {
}


// ATOM 

proof fn monotonicMult(c: real, x: real, y: real)
    requires x < y && c > 0.0
    ensures c * x < c * y
{
}



// ATOM 


proof fn monotonicSquare(x: real, y: real)
    requires 0.0 < x < y
    ensures 0.0 < x * x < y * y
{
    monotonicMult(x, x, y);
}