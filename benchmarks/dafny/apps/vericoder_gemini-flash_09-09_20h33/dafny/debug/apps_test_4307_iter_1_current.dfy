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
function CountDivisors(n: nat): nat
    requires n > 0
{
    var count := 0;
    var i := 1;
    while i * i <= n
        invariant 1 <= i <= n + 1
        invariant forall d :: 1 <= d < i && n % d == 0 ==> count + count Divisors(n/d) contains d
        invariant count == |set d | 1 <= d < i && n % d == 0|
    {
        if n % i == 0 {
            count := count + 1;
            if i * i != n {
                count := count + 1;
            }
        }
        i := i + 1;
    }
    return count;
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
  var count := 0;
  var i := 1;
  while i <= N
    invariant 0 <= count <= 5
    invariant 1 <= i <= N + 1
    invariant (i < 105) ==> count == 0
    invariant (105 <= i < 135) ==> count == 1
    invariant (135 <= i < 165) ==> count == 2
    invariant (165 <= i < 189) ==> count == 3
    invariant (189 <= i < 195) ==> count == 4
    invariant (i >= 195) ==> count == 5
    invariant (i <= N && IsOdd(i) && HasEightDivisors(i)) ==> (N >= 105 ? count >= 1 : count == 0)
    invariant forall k :: 1 <= k < i && IsOdd(k) && HasEightDivisors(k) ==> (k == 105 || k == 135 || k == 165 || k == 189 || k == 195)
    invariant count == CountOddWithEightDivisors(i-1)
  {
    if IsOdd(i) && HasEightDivisors(i) {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>

