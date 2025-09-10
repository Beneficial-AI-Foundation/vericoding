predicate ValidInput(a: int, b: int, c: int, d: int) {
    a > 0 && b > 0 && c > 0 && d > 0
}

predicate IsValidFractionString(s: string, num: int, den: int) {
    num >= 0 && den > 0 && 
    gcd(num, den) == 1 &&
    s == intToString(num) + "/" + intToString(den)
}

// <vc-helpers>
function gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function abs(n: int): int
{
    if n >= 0 then n else -n
}

function intToString(n: int): string
    decreases if n >= 0 then n else -n + 1
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else if n > 9 then intToString(n / 10) + intToString(n % 10)
    else "-" + intToString(-n)
}

lemma GcdCommutative(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures gcd(a, b) == gcd(b, a)
{
}

lemma GcdPositive(a: int, b: int)
    requires a >= 0 && b >= 0
    requires a > 0 || b > 0
    ensures gcd(a, b) > 0
{
    if a == 0 {
        assert gcd(a, b) == b;
        assert b > 0;
    } else if b == 0 {
        assert gcd(a, b) == a;
        assert a > 0;
    }
}

lemma GcdDivides(a: int, b: int)
    requires a >= 0 && b >= 0
    requires a > 0 || b > 0
    ensures gcd(a, b) > 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
    decreases a + b
{
    GcdPositive(a, b);
    var g := gcd(a, b);
    
    if a == 0 {
        assert g == b;
        assert a % g == 0 % b == 0;
        assert b % g == b % b == 0;
    } else if b == 0 {
        assert g == a;
        assert a % g == a % a == 0;
        assert b % g == 0 % a == 0;
    } else if a > b {
        GcdDivides(a - b, b);
        assert g == gcd(a - b, b);
        assert (a - b) % g == 0;
        assert b % g == 0;
        assert a % g == ((a - b) + b) % g == 0;
    } else {
        GcdDivides(a, b - a);
        assert g == gcd(a, b - a);
        assert a % g == 0;
        assert (b - a) % g == 0;
        assert b % g == ((b - a) + a) % g == 0;
    }
}

lemma GcdReduction(a: int, b: int, g: int)
    requires a >= 0 && b >= 0 && g > 0
    requires g == gcd(a, b)
    requires a > 0 || b > 0
    ensures a % g == 0 && b % g == 0
    ensures gcd(a / g, b / g) == 1
{
    GcdDivides(a, b);
    assert a % g == 0 && b % g == 0;
    
    var a' := a / g;
    var b' := b / g;
    
    var d := gcd(a', b');
    
    if d > 1 {
        // If d > 1, then d * g would be a common divisor of a and b
        // that is greater than g, contradicting that g is the GCD
        assert a' % d == 0 && b' % d == 0 by {
            if a' > 0 || b' > 0 {
                GcdDivides(a', b');
            }
        }
        assert a == a' * g;
        assert b == b' * g;
        assert a % (d * g) == 0;
        assert b % (d * g) == 0;
        // This contradicts g being the GCD since d * g > g
        assert false;
    }
    assert d == 1;
}

lemma GcdIsMaxDivisor(a: int, b: int, g: int, d: int)
    requires a >= 0 && b >= 0
    requires a > 0 || b > 0
    requires g == gcd(a, b)
    requires d > 0 && a % d == 0 && b % d == 0
    ensures d <= g
{
    // The GCD is the greatest common divisor by definition
    // Any common divisor d must divide the GCD
    // We prove this by considering that gcd(a/d, b/d) exists
    var a' := a / d;
    var b' := b / d;
    assert a == a' * d;
    assert b == b' * d;
    var g' := gcd(a', b');
    assert g == g' * d;
    assert d <= g;
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: string)
    requires ValidInput(a, b, c, d)
    ensures a * d == b * c ==> result == "0/1"
    ensures a * d > b * c ==> exists numerator, denominator :: 
        numerator > 0 && denominator > 0 && 
        gcd(numerator, denominator) == 1 &&
        result == intToString(numerator) + "/" + intToString(denominator) &&
        numerator * a * d == (a * d - b * c) * denominator
    ensures a * d < b * c ==> exists numerator, denominator :: 
        numerator > 0 && denominator > 0 && 
        gcd(numerator, denominator) == 1 &&
        result == intToString(numerator) + "/" + intToString(denominator) &&
        numerator * b * c == (b * c - a * d) * denominator
// </vc-spec>
// <vc-code>
{
    var ad := a * d;
    var bc := b * c;
    
    if ad == bc {
        result := "0/1";
    } else if ad > bc {
        var numerator := ad - bc;
        var denominator := ad;
        assert numerator > 0 && denominator > 0;
        
        var g := gcd(numerator, denominator);
        GcdPositive(numerator, denominator);
        assert g > 0;
        GcdDivides(numerator, denominator);
        
        var num_reduced := numerator / g;
        var den_reduced := denominator / g;
        
        GcdReduction(numerator, denominator, g);
        assert gcd(num_reduced, den_reduced) == 1;
        assert num_reduced * ad == (ad - bc) * den_reduced;
        
        result := intToString(num_reduced) + "/" + intToString(den_reduced);
    } else {
        var numerator := bc - ad;
        var denominator := bc;
        assert numerator > 0 && denominator > 0;
        
        var g := gcd(numerator, denominator);
        GcdPositive(numerator, denominator);
        assert g > 0;
        GcdDivides(numerator, denominator);
        
        var num_reduced := numerator / g;
        var den_reduced := denominator / g;
        
        GcdReduction(numerator, denominator, g);
        assert gcd(num_reduced, den_reduced) == 1;
        assert num_reduced * bc == (bc - ad) * den_reduced;
        
        result := intToString(num_reduced) + "/" + intToString(den_reduced);
    }
}
// </vc-code>

