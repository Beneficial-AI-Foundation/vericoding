pub fn SumOfDigits(number: nat) -> (sum: nat)
    requires(number >= 0)
    ensures(sum >= 0)
    ensures(sum == SumDigits(number))
{
}

proof fn X(x: nat)
    ensures(Power10(NumberOfDigits(x)) > x)
{
}

proof fn NumberIdentity(number: nat, pmax: nat)
    requires(pmax == Power10(NumberOfDigits(number)))
    ensures(number == number % pmax)
{
}

proof fn InIntValues(n: nat)
    ensures(IntValues(n).contains(0))
    ensures(IntValues(n).contains(n))
    ensures(IntValues(n).contains(n/10))
{
}

spec fn IntValues(n: int) -> (r: Seq<int>)
    requires(n >= 0)
    ensures(r.contains(0))
    ensures(r.contains(n))
    ensures(r.contains(n/10))
{
}

spec fn Power10(n: nat) -> (r: nat)
    ensures(r >= 1)
    ensures(n > 0 ==> r % 10 == 0)
{
}

spec fn NumberToSeq(number: int) -> Seq<int>
    requires(number >= 0)
{
}

spec fn Sum(digits: Seq<int>) -> int
{
}

spec fn SumDigits(n: nat) -> nat
{
}

spec fn SumDigitsRecursive(n: nat, p: nat) -> (r: nat)
{
}

spec fn NumberOfDigits(n: nat) -> (r: nat)
    ensures(r >= 1)
    ensures(r == 1 <==> (0 <= n <= 9))
{
}