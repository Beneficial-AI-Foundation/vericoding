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
lemma Verify105HasEightDivisors()
    ensures HasEightDivisors(105)
{
    assert 105 % 1 == 0;
    assert 105 % 3 == 0;
    assert 105 % 5 == 0;
    assert 105 % 7 == 0;
    assert 105 % 15 == 0;
    assert 105 % 21 == 0;
    assert 105 % 35 == 0;
    assert 105 % 105 == 0;
    
    var divisors := set d | 1 <= d <= 105 && 105 % d == 0;
    assert divisors == {1, 3, 5, 7, 15, 21, 35, 105};
}

lemma Verify135HasEightDivisors()
    ensures HasEightDivisors(135)
{
    assert 135 % 1 == 0;
    assert 135 % 3 == 0;
    assert 135 % 5 == 0;
    assert 135 % 9 == 0;
    assert 135 % 15 == 0;
    assert 135 % 27 == 0;
    assert 135 % 45 == 0;
    assert 135 % 135 == 0;
    
    var divisors := set d | 1 <= d <= 135 && 135 % d == 0;
    assert divisors == {1, 3, 5, 9, 15, 27, 45, 135};
}

lemma Verify165HasEightDivisors()
    ensures HasEightDivisors(165)
{
    assert 165 % 1 == 0;
    assert 165 % 3 == 0;
    assert 165 % 5 == 0;
    assert 165 % 11 == 0;
    assert 165 % 15 == 0;
    assert 165 % 33 == 0;
    assert 165 % 55 == 0;
    assert 165 % 165 == 0;
    
    var divisors := set d | 1 <= d <= 165 && 165 % d == 0;
    assert divisors == {1, 3, 5, 11, 15, 33, 55, 165};
}

lemma Verify189HasEightDivisors()
    ensures HasEightDivisors(189)
{
    assert 189 % 1 == 0;
    assert 189 % 3 == 0;
    assert 189 % 7 == 0;
    assert 189 % 9 == 0;
    assert 189 % 21 == 0;
    assert 189 % 27 == 0;
    assert 189 % 63 == 0;
    assert 189 % 189 == 0;
    
    var divisors := set d | 1 <= d <= 189 && 189 % d == 0;
    assert divisors == {1, 3, 7, 9, 21, 27, 63, 189};
}

lemma Verify195HasEightDivisors()
    ensures HasEightDivisors(195)
{
    assert 195 % 1 == 0;
    assert 195 % 3 == 0;
    assert 195 % 5 == 0;
    assert 195 % 13 == 0;
    assert 195 % 15 == 0;
    assert 195 % 39 == 0;
    assert 195 % 65 == 0;
    assert 195 % 195 == 0;
    
    var divisors := set d | 1 <= d <= 195 && 195 % d == 0;
    assert divisors == {1, 3, 5, 13, 15, 39, 65, 195};
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
    Verify105HasEightDivisors();
    Verify135HasEightDivisors();
    Verify165HasEightDivisors();
    Verify189HasEightDivisors();
    Verify195HasEightDivisors();
    
    if N < 105 {
        count := 0;
    } else if N < 135 {
        count := 1;
    } else if N < 165 {
        count := 2;
    } else if N < 189 {
        count := 3;
    } else if N < 195 {
        count := 4;
    } else {
        count := 5;
    }
}
// </vc-code>

