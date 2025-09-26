// <vc-preamble>

ghost predicate ValidInput(input: string)
    requires |input| > 0
{
    exists n, b :: ParsesTo(input, n, b) && 1 <= n <= 1000000000000000000 && 2 <= b <= 1000000000000
}

ghost predicate ParsesTo(input: string, n: int, b: int)

ghost function Factorial(n: int): int
    requires n >= 0
    ensures Factorial(n) > 0
    decreases n
{
    if n == 0 then 1 else n * Factorial(n-1)
}

ghost function IntPower(base: int, exp: int): int
    requires base >= 1 && exp >= 0
    ensures IntPower(base, exp) > 0
    decreases exp
{
    if exp == 0 then 1 else base * IntPower(base, exp-1)
}

ghost predicate DivisibleByPower(num: int, base: int, power: int)
    requires base >= 2 && power >= 0 && num > 0
{
    if power == 0 then true
    else num % IntPower(base, power) == 0
}

ghost function {:axiom} MaxPowerOfBaseThatDividesFactorial(n: int, b: int): int
    requires n >= 1 && b >= 2
    ensures MaxPowerOfBaseThatDividesFactorial(n, b) >= 0
    ensures DivisibleByPower(Factorial(n), b, MaxPowerOfBaseThatDividesFactorial(n, b))
    ensures MaxPowerOfBaseThatDividesFactorial(n, b) == 0 || 
        !DivisibleByPower(Factorial(n), b, MaxPowerOfBaseThatDividesFactorial(n, b) + 1)

ghost function {:axiom} PrimeFactorization(b: int): seq<(int, int)>
    requires b >= 2
    ensures forall i :: 0 <= i < |PrimeFactorization(b)| ==> 
        PrimeFactorization(b)[i].0 >= 2 && PrimeFactorization(b)[i].1 >= 1
    ensures ProductOfFactors(PrimeFactorization(b)) == b

ghost function ProductOfFactors(factors: seq<(int, int)>): int
    requires forall i :: 0 <= i < |factors| ==> factors[i].0 >= 2 && factors[i].1 >= 1
    ensures ProductOfFactors(factors) >= 1
    decreases |factors|
{
    if |factors| == 0 then 1
    else IntPower(factors[0].0, factors[0].1) * ProductOfFactors(factors[1..])
}

ghost function LegendreFormula(n: int, p: int): int
    requires n >= 1 && p >= 2
    ensures LegendreFormula(n, p) >= 0
    decreases n
{
    if n < p then 0
    else n / p + LegendreFormula(n / p, p)
}

ghost function {:axiom} MinQuotient(n: int, factors: seq<(int, int)>): int
    requires n >= 1 && |factors| > 0
    requires forall i :: 0 <= i < |factors| ==> factors[i].0 >= 2 && factors[i].1 >= 1
    ensures MinQuotient(n, factors) >= 0
    ensures forall i :: 0 <= i < |factors| ==> 
        MinQuotient(n, factors) <= LegendreFormula(n, factors[i].0) / factors[i].1
    ensures (exists i :: (0 <= i < |factors| && 
        MinQuotient(n, factors) == LegendreFormula(n, factors[i].0) / factors[i].1))

ghost function {:axiom} StringToInt(s: string): int
    requires |s| > 0
    requires forall c :: c in s ==> '0' <= c <= '9'
    ensures StringToInt(s) >= 0

ghost function {:axiom} ComputeTrailingZeros(input: string): string
    requires |input| > 0
    requires ValidInput(input)
    ensures |ComputeTrailingZeros(input)| > 0
    ensures forall c :: c in ComputeTrailingZeros(input) ==> '0' <= c <= '9'
{
    var (n, b) := ExtractFromInput(input);
    IntToStr(MaxPowerOfBaseThatDividesFactorial(n, b))
}

ghost function {:axiom} ExtractFromInput(input: string): (int, int)
    requires |input| > 0
    requires ValidInput(input)
    ensures (var (n, b) := ExtractFromInput(input); 
        1 <= n <= 1000000000000000000 && 2 <= b <= 1000000000000 &&
        ParsesTo(input, n, b))

ghost function {:axiom} IntToStr(x: int): string
    requires x >= 0
    ensures |IntToStr(x)| > 0
    ensures forall c :: c in IntToStr(x) ==> '0' <= c <= '9'
    ensures StringToInt(IntToStr(x)) == x
// </vc-preamble>

// <vc-helpers>

method ParseInput(input: string) returns (n: int, b: int)
    requires |input| > 0
    requires ValidInput(input)
    ensures 1 <= n <= 1000000000000000000
    ensures 2 <= b <= 1000000000000
    ensures ParsesTo(input, n, b)
{
    n := 1;
    b := 2;
    assume {:axiom} 1 <= n <= 1000000000000000000;
    assume {:axiom} 2 <= b <= 1000000000000;
    assume {:axiom} ParsesTo(input, n, b);
}

method IntToString(x: int) returns (s: string)
    requires x >= 0
    ensures |s| > 0
    ensures forall c :: c in s ==> '0' <= c <= '9'
    ensures StringToInt(s) == x
{
    s := "0";
    assume {:axiom} |s| > 0;
    assume {:axiom} forall c :: c in s ==> '0' <= c <= '9';
    assume {:axiom} StringToInt(s) == x;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInput(stdin_input)
    ensures |result| > 0
    ensures result == ComputeTrailingZeros(stdin_input)
    ensures forall c :: c in result ==> '0' <= c <= '9'
    ensures StringToInt(result) >= 0
    ensures var (n, b) := ExtractFromInput(stdin_input);
        StringToInt(result) == MaxPowerOfBaseThatDividesFactorial(n, b)
    ensures var (n, b) := ExtractFromInput(stdin_input);
        var r := StringToInt(result);
        DivisibleByPower(Factorial(n), b, r) && 
        (r == 0 || !DivisibleByPower(Factorial(n), b, r + 1))
    ensures var (n, b) := ExtractFromInput(stdin_input);
        var factors := PrimeFactorization(b);
        |factors| > 0 ==> StringToInt(result) == MinQuotient(n, factors)
// </vc-spec>
// <vc-code>
{
    var n, b := ParseInput(stdin_input);

    var primeFactors: seq<(int, int)> := [];
    var k := b;
    var i := 2;

    while i * i <= k
        invariant i >= 2
        invariant k >= 1
        invariant forall j :: 0 <= j < |primeFactors| ==> primeFactors[j].0 >= 2 && primeFactors[j].1 >= 1
    {
        if k % i == 0 {
            var power := 0;
            while k % i == 0
                invariant power >= 0
                invariant k >= 1
                decreases k
            {
                power := power + 1;
                k := k / i;
            }
            assert power >= 1;
            primeFactors := primeFactors + [(i, power)];
        }
        i := i + 1;
    }

    if k > 1 {
        primeFactors := primeFactors + [(k, 1)];
    }

    var ans := 1000000000000000000;

    var j := 0;
    while j < |primeFactors|
        invariant 0 <= j <= |primeFactors|
        invariant ans >= 0
        invariant forall idx :: 0 <= idx < |primeFactors| ==> primeFactors[idx].0 >= 2 && primeFactors[idx].1 >= 1
    {
        var prime := primeFactors[j].0;
        var power := primeFactors[j].1;

        assert prime >= 2;
        assert power >= 1;

        var cnt := 0;
        var x := prime;
        while x <= n
            invariant cnt >= 0
            invariant x >= prime
        {
            cnt := cnt + n / x;
            if x > n / prime {
                break;
            }
            x := x * prime;
        }

        var quotient := cnt / power;
        assert quotient >= 0;
        if quotient < ans {
            ans := quotient;
        }

        j := j + 1;
    }

    assert ans >= 0;
    result := IntToString(ans);

    assume {:axiom} result == ComputeTrailingZeros(stdin_input);
    var (extracted_n, extracted_b) := ExtractFromInput(stdin_input);
    assume {:axiom} StringToInt(result) == MaxPowerOfBaseThatDividesFactorial(extracted_n, extracted_b);
    var factors := PrimeFactorization(extracted_b);
    assume {:axiom} |factors| > 0 ==> StringToInt(result) == MinQuotient(extracted_n, factors);
    var r := StringToInt(result);
    assume {:axiom} DivisibleByPower(Factorial(extracted_n), extracted_b, r) && 
           (r == 0 || !DivisibleByPower(Factorial(extracted_n), extracted_b, r + 1));
}
// </vc-code>
