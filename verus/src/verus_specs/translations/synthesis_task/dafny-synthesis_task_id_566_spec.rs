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
    if n == 0 { seq![0] }
    else { seq![n] + IntValues(n/10) }
}

spec fn Power10(n: nat) -> (r: nat)
    ensures(r >= 1)
    ensures(n > 0 ==> r % 10 == 0)
{
    if (n == 0) { 1 } else { 10 * Power10(n-1) }
}

spec fn NumberToSeq(number: int) -> Seq<int>
    requires(number >= 0)
{
    if number == 0 { seq![] }
    else { seq![number % 10] + NumberToSeq(number/10) }
}

spec fn Sum(digits: Seq<int>) -> int
{
    if digits.len() == 0 { 0 } else { digits[0] + Sum(digits.subrange(1, digits.len() as int)) }
}

spec fn SumDigits(n: nat) -> nat
{
    let ndigits = NumberOfDigits(n);
    let p = Power10(ndigits-1);
    SumDigitsRecursive(n, p)
}

spec fn SumDigitsRecursive(n: nat, p: nat) -> (r: nat)
{
    if n == 0 || p == 0 { 0 }
    else {
        let leftMostDigit = n/p;
        let rest = n%p;
        leftMostDigit + SumDigitsRecursive(rest, p/10)
    }
}

spec fn NumberOfDigits(n: nat) -> (r: nat)
    ensures(r >= 1)
    ensures(r == 1 <==> (0 <= n <= 9))
{
    if 0 <= n <= 9 { 1 } else { 1 + NumberOfDigits(n/10) }
}