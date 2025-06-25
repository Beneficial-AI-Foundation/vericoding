// SPEC 
pub fn mroot1(n: int) -> (r: int) //Cost O(root n)
    requires(n >= 0)
    ensures(|r: int| r >= 0 && r * r <= n < (r + 1) * (r + 1))
{
}

// SPEC 
pub fn mroot2(n: int) -> (r: int) //Cost O(n)
    requires(n >= 0)
    ensures(|r: int| r >= 0 && r * r <= n < (r + 1) * (r + 1))
{
}

// SPEC 
pub fn mroot3(n: int) -> (r: int) //Cost O(log n)
    requires(n >= 0)
    ensures(|r: int| r >= 0 && r * r <= n < (r + 1) * (r + 1))
{
}