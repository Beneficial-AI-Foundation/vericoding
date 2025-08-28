//lemma DivIsZero()
//  ensures forall num, den : nat :: den >= 1 && num < den ==> num/den == 0

// ghost function ValuesOfn(number: nat, ndigits: nat) : (r: seq<nat>)
// {
//   seq(ndigits+1, i requires 0 <= i <= ndigits => number / PowersOfTen[i])
// }

ghost function IntValues(n: int) : (r: seq<int>)
  requires n >= 0
  ensures 0 in r
  ensures n in r
  ensures n/10 in r
  //    ensures forall p :: p in powersOfTen ==> n/p in r
{
  if n == 0 then [0]
  else [n] + IntValues(n/10)
}

function Power10(n: nat): (r: nat)
  ensures r >= 1
  ensures n > 0 ==> r % 10 == 0
{
  if (n == 0) then 1 else 10 * Power10(n-1)
}

function NumberToSeq(number: int) : seq<int>
  requires number >= 0
{
  if number == 0 then []
  else [number % 10] + NumberToSeq(number/10)
}

function Sum(digits: seq<int>) : int
{
  if |digits| == 0 then 0 else digits[0] + Sum(digits[1..])
}

function SumDigits(n: nat) : nat
{
  var ndigits := NumberOfDigits(n);
  var p := Power10(ndigits-1);
  SumDigitsRecursive(n, p)
}

function SumDigitsRecursive(n: nat, p: nat) : (r: nat)
{
  if n == 0 || p == 0 then 0
  else
    var leftMostDigit := n/p;
    var rest := n%p;
    leftMostDigit + SumDigitsRecursive(rest, p/10)

}

function NumberOfDigits(n: nat) : (r: nat)
  ensures r >= 1
  ensures r == 1 <==> 0 <= n <= 9
{
  if 0 <= n <= 9 then 1 else 1+NumberOfDigits(n/10)
}

// <vc-helpers>
lemma SumDigitsRecursiveCorrectness(n: nat, p: nat)
  requires p > 0 ==> exists k :: p == Power10(k)
  ensures SumDigitsRecursive(n, p) >= 0
  decreases n + p
{
  if n == 0 || p == 0 {
  } else {
    var leftMostDigit := n/p;
    var rest := n%p;
    assert rest < n || p/10 < p;
    SumDigitsRecursiveCorrectness(rest, p/10);
  }
}

lemma SumDigitsNonNegative(n: nat)
  ensures SumDigits(n) >= 0
{
  var ndigits := NumberOfDigits(n);
  var p := Power10(ndigits-1);
  SumDigitsRecursiveCorrectness(n, p);
}

lemma SumDigitsDecomposition(n: nat)
  requires n > 0
  ensures SumDigits(n) == (n % 10) + SumDigits(n / 10)
{
  var ndigits := NumberOfDigits(n);
  var p := Power10(ndigits-1);
  
  if ndigits == 1 {
    assert n <= 9;
    assert n / 10 == 0;
    assert SumDigits(n / 10) == 0;
  } else {
    SumDigitsDecompositionHelper(n, p);
  }
}

lemma Power10PositiveK(k: nat)
  requires k > 0
  ensures Power10(k) >= 10
{
}

lemma SumDigitsDecompositionHelper(n: nat, p: nat)
  requires n > 0
  requires p > 0
  requires exists k :: k > 0 && p == Power10(k)
  ensures SumDigitsRecursive(n, p) == (n % 10) + SumDigitsRecursive(n / 10, p / 10)
  decreases p
{
  if p == 10 {
    var digit := n % 10;
    var quotient := n / 10;
    assert SumDigitsRecursive(n, 10) == (n / 10) + SumDigitsRecursive(n % 10, 1);
    assert SumDigitsRecursive(n % 10, 1) == n % 10;
    assert SumDigitsRecursive(quotient, 1) == quotient;
  } else if n < p {
    assert n / p == 0;
    assert SumDigitsRecursive(n, p) == SumDigitsRecursive(n, p / 10);
    SumDigitsDecompositionHelper(n, p / 10);
  } else {
    var leftMostDigit := n / p;
    var rest := n % p;
    assert SumDigitsRecursive(n, p) == leftMostDigit + SumDigitsRecursive(rest, p / 10);
    SumDigitsDecompositionHelper(rest, p / 10);
    assert n % 10 == rest % 10;
    assert n / 10 == (leftMostDigit * p + rest) / 10;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if number == 0 {
    sum := 0;
    return;
  }
  
  var remaining := number;
  sum := 0;
  
  while remaining > 0
    invariant remaining >= 0
    invariant sum >= 0
    invariant sum + SumDigits(remaining) == SumDigits(number)
    decreases remaining
  {
    var digit := remaining % 10;
    sum := sum + digit;
    var newRemaining := remaining / 10;
    
    SumDigitsDecomposition(remaining);
    
    remaining := newRemaining;
  }
  
  SumDigitsNonNegative(number);
}
// </vc-code>
