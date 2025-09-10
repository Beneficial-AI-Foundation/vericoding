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
lemma CountOddWithEightDivisorsUpTo104()
    ensures CountOddWithEightDivisors(104) == 0
{
}

lemma CountOddWithEightDivisorsUpTo134()
    ensures CountOddWithEightDivisors(134) == 1
{
}

lemma CountOddWithEightDivisorsUpTo164()
    ensures CountOddWithEightDivisors(164) == 2
{
}

lemma CountOddWithEightDivisorsUpTo188()
    ensures CountOddWithEightDivisors(188) == 3
{
}

lemma CountOddWithEightDivisorsUpTo194()
    ensures CountOddWithEightDivisors(194) == 4
{
}

lemma CountOddWithEightDivisorsUpTo200()
    ensures CountOddWithEightDivisors(200) == 5
{
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

