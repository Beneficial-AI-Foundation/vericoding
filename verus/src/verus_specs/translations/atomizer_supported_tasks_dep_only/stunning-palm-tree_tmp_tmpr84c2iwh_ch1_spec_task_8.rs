// Ex 1.3
//ATOM_PLACEHOLDER_Triple

//ATOM_PLACEHOLDER_Caller

// Ex 1.6
//ATOM_PLACEHOLDER_MinUnderSpec

//ATOM_PLACEHOLDER_Min

// Ex 1.7
// SPEC 

// Ex 1.7
pub fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures(s == x + y),
    ensures(x <= m && y <= m),
    ensures(m == x || m == y),
{
}
// SPEC 

// Ex 1.7
pub fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures(s == x + y),
    ensures(x <= m && y <= m),
    ensures(m == x || m == y),
{
}

// Ex 1.8
// SPEC 

// Ex 1.8
pub fn ReconstructFromMaxSum(s: int, m: int) -> (x: int, y: int)
    // requires(0 < s && s / 2 < m && m < s),
    requires(s - m <= m),
    ensures(s == x + y),
    ensures((m == y || m == x) && x <= m && y <= m),
{
}

// SPEC 

pub fn TestMaxSum(x: int, y: int)
    // requires(x > 0 && y > 0 && x != y),
{
}

// Ex 1.9
//ATOM_PLACEHOLDER_Average

//ATOM_PLACEHOLDER_Triple'