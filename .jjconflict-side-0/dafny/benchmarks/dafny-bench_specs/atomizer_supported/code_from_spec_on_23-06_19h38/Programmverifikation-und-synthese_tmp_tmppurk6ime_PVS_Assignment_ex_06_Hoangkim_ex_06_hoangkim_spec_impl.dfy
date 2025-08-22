//ATOM gcd_function
ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd'(x - y, y)
    else gcd'(y, x)
}

/* code modified by LLM (iteration 3): added helper lemma to prove GCD property when first argument is larger */
lemma gcd_subtract_first(a: int, b: int)
    requires a > b > 0
    ensures gcd'(a - b, b) == gcd'(a, b)
{
    // This follows directly from the definition of gcd'
}

/* code modified by LLM (iteration 3): added helper lemma to prove GCD property when second argument is larger */
lemma gcd_subtract_second(a: int, b: int)
    requires 0 < a < b
    ensures gcd'(a, b - a) == gcd'(a, b)
{
    // By definition: gcd'(a, b) = gcd'(b, a) since a < b
    // And gcd'(b, a) = gcd'(b - a, a) since b > a
    // So gcd'(a, b) = gcd'(b - a, a) = gcd'(a, b - a) by symmetry
}

//IMPL gcdI
method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd'(m, n)
{
    var a := m;
    var b := n;
    
    /* code modified by LLM (iteration 3): kept the correct decreases clause */
    while a != b
        invariant a > 0 && b > 0
        invariant gcd'(a, b) == gcd'(m, n)
        decreases if a > b then a else b
    {
        if a > b {
            /* code modified by LLM (iteration 3): call helper lemma to establish GCD property */
            gcd_subtract_first(a, b);
            a := a - b;
        } else {
            /* code modified by LLM (iteration 3): call helper lemma to establish GCD property */
            gcd_subtract_second(a, b);
            b := b - a;
        }
    }
    
    d := a;
}