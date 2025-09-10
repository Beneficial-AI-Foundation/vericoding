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
lemma LemmaCountOddWithEightDivisors(N: nat, M: nat)
    requires 0 < N <= M
    ensures CountOddWithEightDivisors(N) <= CountOddWithEightDivisors(M)
{
}

lemma LemmaKnownValues()
    ensures CountOddWithEightDivisors(104) == 0
    ensures CountOddWithEightDivisors(105) == 1
    ensures CountOddWithEightDivisors(134) == 1
    ensures CountOddWithEightDivisors(135) == 2
    ensures CountOddWithEightDivisors(164) == 2
    ensures CountOddWithEightDivisors(165) == 3
    ensures CountOddWithEightDivisors(188) == 3
    ensures CountOddWithEightDivisors(189) == 4
    ensures CountOddWithEightDivisors(194) == 4
    ensures CountOddWithEightDivisors(195) == 5
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
  LemmaKnownValues();
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

