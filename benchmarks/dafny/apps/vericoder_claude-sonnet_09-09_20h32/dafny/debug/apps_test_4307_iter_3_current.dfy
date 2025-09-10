predicate IsOdd(n: int) {
    n % 2 == 1
}

function CountDivisors(n: nat): nat
    requires n > 0
{
    |set d | 1 <= d <= n && n % d == 0|
}

predicate HasEightDivisors(n: nat)
    requires n > 0
{
    CountDivisors(n) == 8
}

function CountOddWithEightDivisors(N: nat): nat {
    |set i | 1 <= i <= N && IsOdd(i) && i > 0 && HasEightDivisors(i)|
}

predicate ValidInput(N: int) {
    1 <= N <= 200
}

// <vc-helpers>
lemma DivisorCount105()
    ensures CountDivisors(105) == 8
{
    assert 105 == 3 * 5 * 7;
    var divs := set d | 1 <= d <= 105 && 105 % d == 0;
    assert divs == {1, 3, 5, 7, 15, 21, 35, 105};
    assert |divs| == 8;
}

lemma DivisorCount135()
    ensures CountDivisors(135) == 8
{
    assert 135 == 3 * 3 * 3 * 5;
    assert 135 == 27 * 5;
    var divs := set d | 1 <= d <= 135 && 135 % d == 0;
    assert divs == {1, 3, 5, 9, 15, 27, 45, 135};
    assert |divs| == 8;
}

lemma DivisorCount165()
    ensures CountDivisors(165) == 8
{
    assert 165 == 3 * 5 * 11;
    var divs := set d | 1 <= d <= 165 && 165 % d == 0;
    assert divs == {1, 3, 5, 11, 15, 33, 55, 165};
    assert |divs| == 8;
}

lemma DivisorCount189()
    ensures CountDivisors(189) == 8
{
    assert 189 == 3 * 3 * 3 * 7;
    assert 189 == 27 * 7;
    var divs := set d | 1 <= d <= 189 && 189 % d == 0;
    assert divs == {1, 3, 7, 9, 21, 27, 63, 189};
    assert |divs| == 8;
}

lemma DivisorCount195()
    ensures CountDivisors(195) == 8
{
    assert 195 == 3 * 5 * 13;
    var divs := set d | 1 <= d <= 195 && 195 % d == 0;
    assert divs == {1, 3, 5, 13, 15, 39, 65, 195};
    assert |divs| == 8;
}

lemma CountOddWithEightDivisorsUpTo104()
    ensures CountOddWithEightDivisors(104) == 0
{
    var s := set i | 1 <= i <= 104 && IsOdd(i) && i > 0 && HasEightDivisors(i);
    assert s == {};
}

lemma CountOddWithEightDivisorsUpTo134()
    ensures CountOddWithEightDivisors(134) == 1
{
    DivisorCount105();
    var s := set i | 1 <= i <= 134 && IsOdd(i) && i > 0 && HasEightDivisors(i);
    assert 105 in s;
    assert s == {105};
}

lemma CountOddWithEightDivisorsUpTo164()
    ensures CountOddWithEightDivisors(164) == 2
{
    DivisorCount105();
    DivisorCount135();
    var s := set i | 1 <= i <= 164 && IsOdd(i) && i > 0 && HasEightDivisors(i);
    assert 105 in s;
    assert 135 in s;
    assert s == {105, 135};
}

lemma CountOddWithEightDivisorsUpTo188()
    ensures CountOddWithEightDivisors(188) == 3
{
    DivisorCount105();
    DivisorCount135();
    DivisorCount165();
    var s := set i | 1 <= i <= 188 && IsOdd(i) && i > 0 && HasEightDivisors(i);
    assert 105 in s;
    assert 135 in s;
    assert 165 in s;
    assert s == {105, 135, 165};
}

lemma CountOddWithEightDivisorsUpTo194()
    ensures CountOddWithEightDivisors(194) == 4
{
    DivisorCount105();
    DivisorCount135();
    DivisorCount165();
    DivisorCount189();
    var s := set i | 1 <= i <= 194 && IsOdd(i) && i > 0 && HasEightDivisors(i);
    assert 105 in s;
    assert 135 in s;
    assert 165 in s;
    assert 189 in s;
    assert s == {105, 135, 165, 189};
}

lemma CountOddWithEightDivisorsUpTo200()
    ensures CountOddWithEightDivisors(200) == 5
{
    DivisorCount105();
    DivisorCount135();
    DivisorCount165();
    DivisorCount189();
    DivisorCount195();
    var s := set i | 1 <= i <= 200 && IsOdd(i) && i > 0 && HasEightDivisors(i);
    assert 105 in s;
    assert 135 in s;
    assert 165 in s;
    assert 189 in s;
    assert 195 in s;
    assert s == {105, 135, 165, 189, 195};
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (count: int)
    requires ValidInput(N)
    ensures N < 105 ==> count == 0
    ensures 105 <= N < 135 ==> count == 1
    ensures 135 <= N < 165 ==> count == 2
    ensures 165 <= N < 189 ==> count == 3
    ensures 189 <= N < 195 ==> count == 4
    ensures N >= 195 ==> count == 5
    ensures 0 <= count <= 5
// </vc-spec>
// <vc-code>
{
    if N < 105 {
        CountOddWithEightDivisorsUpTo104();
        count := 0;
    } else if N < 135 {
        CountOddWithEightDivisorsUpTo134();
        count := 1;
    } else if N < 165 {
        CountOddWithEightDivisorsUpTo164();
        count := 2;
    } else if N < 189 {
        CountOddWithEightDivisorsUpTo188();
        count := 3;
    } else if N < 195 {
        CountOddWithEightDivisorsUpTo194();
        count := 4;
    } else {
        CountOddWithEightDivisorsUpTo200();
        count := 5;
    }
}
// </vc-code>

