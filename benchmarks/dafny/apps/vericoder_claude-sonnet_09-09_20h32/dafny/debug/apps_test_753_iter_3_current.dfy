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
    requires a >= 0 && b >= 0 && (a > 0 || b > 0)
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a
    else if a <= b then gcd(a, b - a)
    else gcd(a - b, b)
}

function intToString(n: int): string
    requires n >= 0

lemma GcdProperties(a: int, b: int)
    requires a >= 0 && b >= 0 && (a > 0 || b > 0)
    ensures gcd(a, b) > 0
    ensures gcd(a, b) <= a || a == 0
    ensures gcd(a, b) <= b || b == 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
{
    if a == 0 {
        assert gcd(a, b) == b;
    } else if b == 0 {
        assert gcd(a, b) == a;
    } else {
        if a <= b {
            GcdProperties(a, b - a);
        } else {
            GcdProperties(a - b, b);
        }
    }
}

lemma GcdDivision(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a / gcd(a, b), b / gcd(a, b)) == 1
{
    var g := gcd(a, b);
    GcdProperties(a, b);
    var newA := a / g;
    var newB := b / g;
    
    if newA == 0 {
        assert a < g;
        assert false;
    }
    if newB == 0 {
        assert b < g;
        assert false;
    }
    
    GcdDivisionHelper(a, b, g);
}

lemma GcdDivisionHelper(a: int, b: int, g: int)
    requires a > 0 && b > 0 && g > 0
    requires g == gcd(a, b)
    requires a % g == 0 && b % g == 0
    ensures gcd(a / g, b / g) == 1
{
    var newA := a / g;
    var newB := b / g;
    
    if newA > 0 && newB > 0 {
        var newGcd := gcd(newA, newB);
        if newGcd > 1 {
            assert (newA * g) % (newGcd * g) == 0;
            assert (newB * g) % (newGcd * g) == 0;
            assert newGcd * g > g;
            GcdMinimality(a, b, g, newGcd * g);
            assert false;
        }
    }
}

lemma GcdMinimality(a: int, b: int, g1: int, g2: int)
    requires a > 0 && b > 0 && g1 > 0 && g2 > 0
    requires a % g1 == 0 && b % g1 == 0
    requires a % g2 == 0 && b % g2 == 0
    requires g1 == gcd(a, b) && g2 > g1
    ensures false
{
    GcdMaximality(a, b, g1, g2);
}

lemma GcdMaximality(a: int, b: int, g1: int, g2: int)
    requires a > 0 && b > 0 && g1 > 0 && g2 > 0
    requires a % g1 == 0 && b % g1 == 0
    requires a % g2 == 0 && b % g2 == 0
    requires g1 == gcd(a, b) && g2 > g1
    ensures false
{
    if a == b {
        assert gcd(a, b) == a;
        assert g1 == a;
        assert a % g2 == 0;
        assert g2 <= a;
        assert false;
    } else if a < b {
        assert gcd(a, b) == gcd(a, b - a);
        assert (b - a) % g2 == 0;
        GcdMaximality(a, b - a, g1, g2);
    } else {
        assert gcd(a, b) == gcd(a - b, b);
        assert (a - b) % g2 == 0;
        GcdMaximality(a - b, b, g1, g2);
    }
}

method ReduceFraction(num: int, den: int) returns (reducedNum: int, reducedDen: int)
    requires num > 0 && den > 0
    ensures reducedNum > 0 && reducedDen > 0
    ensures gcd(reducedNum, reducedDen) == 1
    ensures reducedNum * den == num * reducedDen
{
    var g := gcd(num, den);
    GcdProperties(num, den);
    reducedNum := num / g;
    reducedDen := den / g;
    GcdDivision(num, den);
    
    assert num == reducedNum * g;
    assert den == reducedDen * g;
    assert reducedNum * den == reducedNum * reducedDen * g;
    assert num * reducedDen == reducedNum * g * reducedDen;
    assert reducedNum * den == num * reducedDen;
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
    if a * d == b * c {
        result := "0/1";
    } else if a * d > b * c {
        var diff := a * d - b * c;
        assert diff > 0;
        assert a * d > 0;
        var numerator, denominator := ReduceFraction(diff, a * d);
        result := intToString(numerator) + "/" + intToString(denominator);
        assert numerator * (a * d) == diff * denominator;
        assert numerator * a * d == (a * d - b * c) * denominator;
    } else {
        var diff := b * c - a * d;
        assert diff > 0;
        assert b * c > 0;
        var numerator, denominator := ReduceFraction(diff, b * c);
        result := intToString(numerator) + "/" + intToString(denominator);
        assert numerator * (b * c) == diff * denominator;
        assert numerator * b * c == (b * c - a * d) * denominator;
    }
}
// </vc-code>

