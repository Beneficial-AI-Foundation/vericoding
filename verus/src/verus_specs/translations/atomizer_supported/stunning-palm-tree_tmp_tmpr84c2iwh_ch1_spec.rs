// Ex 1.3
// SPEC 

pub fn Triple_prime(x: int) -> (r: int)
    ensures(Average(2*r, 6*x) == 6*x)
{
}

// SPEC 

pub fn Caller()
{
}

// Ex 1.6
// SPEC 

// Ex 1.6
pub fn MinUnderSpec(x: int, y: int) -> (r: int)
    ensures(r <= x && r <= y)
{
}

// SPEC 

pub fn Min(x: int, y: int) -> (r: int)
    ensures(r <= x && r <= y),
    ensures(r == x || r == y)
{
}

// Ex 1.7
// SPEC 

// Ex 1.7
pub fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures(s == x + y),
    ensures(x <= m && y <= m),
    ensures(m == x || m == y)
{
}

pub fn MaxSumCaller()
{
}

// Ex 1.8
// SPEC 

// Ex 1.8
pub fn ReconstructFromMaxSum(s: int, m: int) -> (x: int, y: int)
    requires(s - m <= m),
    ensures(s == x + y),
    ensures((m == y || m == x) && x <= m && y <= m)
{
}

// SPEC 

pub fn TestMaxSum(x: int, y: int)
{
}

// Ex 1.9
// ATOM 

// Ex 1.9
pub fn Average(a: int, b: int) -> int
{
    (a + b) / 2
}