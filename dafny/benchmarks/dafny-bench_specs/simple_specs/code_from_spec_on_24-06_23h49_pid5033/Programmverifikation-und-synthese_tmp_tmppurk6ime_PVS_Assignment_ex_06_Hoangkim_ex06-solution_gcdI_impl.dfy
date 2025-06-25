//ATOM gcd'
ghost function gcd'(x:int,y:int):int
 requires x > 0 && y > 0
{
 if x==y then x
 else if x > y then gcd'(x-y,y)
 else gcd'(y,x)
}

//IMPL gcdI
/* code modified by LLM (iteration 4): Provided proper proofs for helper lemmas */
lemma gcd_subtract_lemma(x: int, y: int)
    requires x > 0 && y > 0 && x > y
    ensures gcd'(x - y, y) == gcd'(x, y)
{
    // From the definition of gcd', when x > y, gcd'(x, y) = gcd'(x - y, y)
    // This is exactly what the definition states
}

lemma gcd_symmetric_lemma(x: int, y: int)
    requires x > 0 && y > 0
    ensures gcd'(x, y) == gcd'(y, x)
{
    // We need to prove this by considering the cases in the definition
    if x == y {
        // gcd'(x, y) = x = y = gcd'(y, x)
    } else if x > y {
        // gcd'(x, y) = gcd'(x - y, y)
        // gcd'(y, x) = gcd'(x, y) (since x > y, so in gcd'(y, x) we go to else branch)
        // We need to show these are equal through the recursive structure
        gcd_symmetric_helper(x, y);
    } else {
        // x < y, so gcd'(x, y) = gcd'(y, x) by definition
        // and gcd'(y, x) = gcd'(y - x, x) since y > x
        gcd_symmetric_helper(y, x);
    }
}

lemma gcd_symmetric_helper(x: int, y: int)
    requires x > 0 && y > 0
    ensures gcd'(x, y) == gcd'(y, x)
    decreases x + y
{
    if x == y {
        // Base case: gcd'(x, x) = x = gcd'(x, x)
    } else if x > y {
        // gcd'(x, y) = gcd'(x - y, y)
        // gcd'(y, x) = gcd'(x, y) (by definition since x > y)
        gcd_symmetric_helper(x - y, y);
    } else {
        // x < y
        // gcd'(x, y) = gcd'(y, x) (by definition)
        // gcd'(y, x) = gcd'(y - x, x) (since y > x)
        gcd_symmetric_helper(x, y - x);
    }
}

method gcdI(m:int, n:int) returns (d:int)
 requires m > 0 && n > 0
 ensures  d == gcd'(m,n) 
{
    var a := m;
    var b := n;
    
    while a != b
        invariant a > 0 && b > 0
        invariant gcd'(a, b) == gcd'(m, n)
        decreases a + b
    {
        if a > b {
            /* code modified by LLM (iteration 4): Apply lemma to maintain invariant when a > b */
            gcd_subtract_lemma(a, b);
            a := a - b;
        } else {
            /* code modified by LLM (iteration 4): Apply symmetry and subtraction lemmas when b > a */
            gcd_symmetric_lemma(a, b);
            gcd_subtract_lemma(b, a);
            gcd_symmetric_lemma(b - a, a);
            b := b - a;
        }
    }
    
    d := a;
}