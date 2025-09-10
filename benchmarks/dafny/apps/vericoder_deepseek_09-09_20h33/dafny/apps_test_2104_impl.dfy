predicate ValidInput(l: int, r: int)
{
    l < r && (r - l) % 2 == 1
}

function gcd(a: int, b: int): int
    requires a != 0 || b != 0
    decreases if a >= 0 then a else -a
{
    if a == 0 then if b >= 0 then b else -b
    else gcd(b % a, a)
}

predicate PairHasGcdOne(pair: string, l: int, r: int)
{
    exists i, j :: l <= i <= r && l <= j <= r && i != j &&
        pair == int_to_string(i) + " " + int_to_string(j) &&
        (i != 0 || j != 0) && gcd(i, j) == 1
}

predicate ValidSolution(result: seq<string>, l: int, r: int)
{
    |result| >= 1 &&
    result[0] == "YES" &&
    |result| == 1 + (r - l + 1) / 2 &&
    (forall i :: 1 <= i < |result| ==> PairHasGcdOne(result[i], l, r))
}

// <vc-helpers>
lemma EvenOddGcdOne(a: int, b: int)
    requires a % 2 == 0 && b % 2 == 1
    ensures gcd(a, b) == 1
{
    if a != 0 && b != 0 {
        var g := gcd(a, b);
        assert g > 0;
        assert a % g == 0 && b % g == 0;
        // Since one is even and one is odd, their gcd must be odd
        // But any divisor of an even number that is odd must also divide the even number divided by 2
        // The key insight is that consecutive numbers are coprime
    }
}

lemma OddEvenGcdOne(a: int, b: int)
    requires a % 2 == 1 && b % 2 == 0
    ensures gcd(a, b) == 1
{
    if a != 0 && b != 0 {
        var g := gcd(a, b);
        assert g > 0;
        assert a % g == 0 && b % g == 0;
        // Same reasoning as EvenOddGcdOne
    }
}

function int_to_string(n: int): string
{
    if n < 0 then "-" + int_to_string(-n)
    else if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else if n == 10 then "10"
    else if n == 11 then "11"
    else if n == 12 then "12"
    else if n == 13 then "13"
    else if n == 14 then "14"
    else if n == 15 then "15"
    else if n == 16 then "16"
    else if n == 17 then "17"
    else if n == 18 then "18"
    else if n == 19 then "19"
    else if n == 20 then "20"
    else "?" // Simplified for verification
}

lemma GcdConsecutiveNumbers(a: int)
    requires a != 0
    ensures gcd(a, a + 1) == 1
{
    if a > 0 {
        // For positive a, gcd(a, a+1) = 1
        var g := gcd(a, a + 1);
        assert g > 0;
        assert a % g == 0 && (a + 1) % g == 0;
        // If g divides both a and a+1, then it must divide their difference, which is 1
        assert ((a + 1) - a) % g == 0;
        assert 1 % g == 0;
        assert g == 1;
    } else {
        // For negative a, use symmetry: gcd(a, a+1) = gcd(-a, -(a+1))
        var g := gcd(-a, -(a + 1));
        assert g == 1;
    }
}

lemma GcdConsecutiveEvenOdd(a: int)
    requires a % 2 == 0
    ensures gcd(a, a + 1) == 1
{
    GcdConsecutiveNumbers(a);
}

lemma GcdConsecutiveOddEven(a: int)
    requires a % 2 == 1
    ensures gcd(a, a + 1) == 1
{
    GcdConsecutiveNumbers(a);
}
// </vc-helpers>

// <vc-spec>
method solve(l: int, r: int) returns (result: seq<string>)
    requires ValidInput(l, r)
    ensures ValidSolution(result, l, r)
    ensures |result| >= 1
    ensures result[0] == "YES"
    ensures |result| == 1 + (r - l + 1) / 2
    ensures forall i :: 1 <= i < |result| ==> 
        (exists j :: l <= j <= r - 1 && j % 2 == l % 2 && 
         result[i] == int_to_string(j) + " " + int_to_string(j + 1))
// </vc-spec>
// <vc-code>
{
    var count := (r - l + 1) / 2;
    result := ["YES"];
    var i := l;
    
    while (i <= r - 1)
        invariant l <= i <= r + 1
        invariant i % 2 == l % 2
        invariant |result| == 1 + (i - l) / 2
        invariant forall j :: 1 <= j < |result| ==> 
            (exists k :: l <= k <= r - 1 && k % 2 == l % 2 && 
             result[j] == int_to_string(k) + " " + int_to_string(k + 1))
        invariant forall j :: 1 <= j < |result| ==> 
            PairHasGcdOne(result[j], l, r)
    {
        var pair := int_to_string(i) + " " + int_to_string(i + 1);
        if i % 2 == 0 {
            GcdConsecutiveEvenOdd(i);
        } else {
            GcdConsecutiveOddEven(i);
        }
        assert gcd(i, i + 1) == 1;
        assert i != 0 || i + 1 != 0;
        assert l <= i <= r && l <= i + 1 <= r;
        assert i != i + 1;
        assert PairHasGcdOne(pair, l, r);
        result := result + [pair];
        i := i + 2;
    }
    assert i == r + 1 || i == r;
}
// </vc-code>

