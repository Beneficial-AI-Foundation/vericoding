//ATOM

/* code modified by LLM (iteration 4): fixed decreases clause using lexicographic ordering to handle x,y swap */
ghost function gcd'(x:int,y:int):int
 requires x > 0 && y > 0
 decreases if x >= y then x else y, if x >= y then y else x
{
 if x==y then x
 else if x > y then gcd'(x-y,y)
 else gcd'(y,x)
}

//IMPL gcdI

method gcdI(m:int, n:int) returns (d:int)
 requires m > 0 && n > 0
 ensures  d == gcd'(m,n) 
{
    var x := m;
    var y := n;
    
    while x != y
        invariant x > 0 && y > 0
        /* code modified by LLM (iteration 4): maintained invariant from previous iteration */
        invariant gcd'(x, y) == gcd'(m, n)
        decreases x + y
    {
        /* code modified by LLM (iteration 4): maintained helper lemma calls from previous iteration */
        if x > y {
            gcd_property_lemma(x, y, x - y, y);
            x := x - y;
        } else {
            gcd_property_lemma(x, y, y - x, x);
            y := y - x;
        }
    }
    
    d := x;
}

/* code modified by LLM (iteration 4): maintained helper lemma from previous iteration */
lemma gcd_property_lemma(a: int, b: int, a': int, b': int)
    requires a > 0 && b > 0 && a' > 0 && b' > 0
    requires (a > b && a' == a - b && b' == b) || (a < b && a' == b - a && b' == a)
    ensures gcd'(a, b) == gcd'(a', b')
{
    if a > b {
        assert a' == a - b && b' == b;
        assert gcd'(a, b) == gcd'(a - b, b);
        assert gcd'(a - b, b) == gcd'(a', b');
    } else {
        assert a < b;  // since a != b from the condition
        assert a' == b - a && b' == a;
        assert gcd'(a, b) == gcd'(b, a);
        assert gcd'(b, a) == gcd'(b - a, a);
        assert gcd'(b - a, a) == gcd'(a', b');
    }
}