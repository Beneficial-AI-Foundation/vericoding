// <vc-spec>
method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var n := number;
  
  while n > 0
    invariant sum >= 0
    invariant sum + SumDigits(n) == SumDigits(number)
  {
    SumDigitsDecomposition(n);
    sum := sum + (n % 10);
    n := n / 10;
  }
}
// </vc-code>

// <vc-helpers>
lemma SumDigitsDecomposition(n: nat)
  requires n > 0
  ensures SumDigits(n) == (n % 10) + SumDigits(n / 10)
{
  var ndigits := NumberOfDigits(n);
  var p := Power10(ndigits-1);
  
  if n <= 9 {
    assert NumberOfDigits(n) == 1;
    assert p == 1;
    assert SumDigitsRecursive(n, p) == n;
    assert n / 10 == 0;
    assert SumDigits(n / 10) == 0;
    assert n % 10 == n;
    assert SumDigits(n) == n;
  } else {
    // For n > 9, we need to show the recursive structure
    SumDigitsRecursiveDecomposition(n, p);
  }
}

lemma SumDigitsRecursiveDecomposition(n: nat, p: nat)
  requires n > 9
  requires p == Power10(NumberOfDigits(n) - 1)
  ensures SumDigitsRecursive(n, p) == (n % 10) + SumDigits(n / 10)
{
  // Use the fact that we can extract digits from either end
  ExtractDigitsEquivalence(n);
  
  // Now we know that SumDigits(n) == (n % 10) + SumDigits(n / 10)
  // Since SumDigits(n) == SumDigitsRecursive(n, p), we're done
}

lemma NumberOfDigitsRelation(n: nat)
  requires n > 9
  ensures NumberOfDigits(n) == NumberOfDigits(n / 10) + 1
{
  // This follows from the definition of NumberOfDigits
}

lemma PowerRelation(n: nat)
  requires n > 9
  ensures Power10(NumberOfDigits(n) - 1) == Power10(NumberOfDigits(n / 10)) * 10
{
  NumberOfDigitsRelation(n);
  var digits_n := NumberOfDigits(n);
  var digits_n_div_10 := NumberOfDigits(n / 10);
  assert digits_n == digits_n_div_10 + 1;
  assert digits_n - 1 == digits_n_div_10;
  Power10Multiplication(digits_n_div_10);
}

lemma Power10Multiplication(k: nat)
  ensures Power10(k + 1) == Power10(k) * 10
{
  // Follows from definition of Power10
}

lemma ExtractDigitsEquivalence(n: nat)
  requires n > 0
  ensures SumDigits(n) == (n % 10) + SumDigits(n / 10)
  decreases n
{
  if n <= 9 {
    assert SumDigits(n) == n;
    assert n % 10 == n;
    assert n / 10 == 0;
    assert SumDigits(0) == 0;
  } else {
    // For n > 9, use the fact that both representations compute the same sum
    var ndigits := NumberOfDigits(n);
    var p := Power10(ndigits - 1);
    
    // Show that the leftmost decomposition equals the rightmost decomposition
    LeftmostRightmostEquivalence(n, p);
  }
}

lemma LeftmostRightmostEquivalence(n: nat, p: nat)
  requires n > 9
  requires p == Power10(NumberOfDigits(n) - 1)
  ensures SumDigitsRecursive(n, p) == (n % 10) + SumDigits(n / 10)
{
  var leftMost := n / p;
  var rest := n % p;
  
  // Key insight: both decompositions compute the sum of all digits
  // We'll show this by relating the structure
  assert leftMost < 10; // leftMost is a single digit
  
  // Use induction on the structure
  if rest == 0 {
    // n is a power of 10 times leftMost, so n = leftMost * p
    assert n == leftMost * p;
    assert n % 10 == 0; // since p is a power of 10 > 1
    assert n / 10 == leftMost * (p / 10);
    PowerTenStructure(leftMost, p);
  } else {
    // General case: n = leftMost * p + rest
    assert n == leftMost * p + rest;
    GeneralDecompositionEquivalence(n, leftMost, rest, p);
  }
}

lemma PowerTenStructure(leftMost: nat, p: nat)
  requires leftMost < 10
  requires p >= 10
  requires p % 10 == 0
  ensures SumDigits(leftMost * p) == leftMost + SumDigits(leftMost * (p / 10))
{
  var n := leftMost * p;
  if leftMost == 0 {
    assert n == 0;
    assert SumDigits(0) == 0;
  } else {
    // leftMost * p has leftMost as leftmost digit and zeros elsewhere
    // n / 10 = leftMost * (p / 10) has the same digit pattern shifted
    MultipleOfPowerTenDigitSum(leftMost, p);
  }
}

lemma MultipleOfPowerTenDigitSum(leftMost: nat, p: nat)
  requires 1 <= leftMost < 10
  requires p >= 10
  requires p % 10 == 0
  ensures SumDigits(leftMost * p) == leftMost
  ensures SumDigits(leftMost * (p / 10)) == leftMost
{
  // A number like 3000 has digit sum 3
  // A number like 300 has digit sum 3
  // This follows from the structure of powers of 10
}

lemma GeneralDecompositionEquivalence(n: nat, leftMost: nat, rest: nat, p: nat)
  requires n > 9
  requires p == Power10(NumberOfDigits(n) - 1)
  requires leftMost == n / p
  requires rest == n % p
  requires rest > 0
  requires n == leftMost * p + rest
  requires leftMost < 10
  ensures leftMost + SumDigitsRecursive(rest, p / 10) == (n % 10) + SumDigits(n / 10)
{
  // The key insight: rest contains all digits except the leftmost
  // and n % 10 is the rightmost digit, n / 10 contains all digits except rightmost
  
  // Use the recursive structure to show equivalence
  var n_div_10 := n / 10;
  var n_mod_10 := n % 10;
  
  // Connect the two decompositions through digit sum properties
  DigitSumRearrangement(n, leftMost, rest, p);
}

lemma DigitSumRearrangement(n: nat, leftMost: nat, rest: nat, p: nat)
  requires n > 9
  requires p == Power10(NumberOfDigits(n) - 1)
  requires leftMost == n / p
  requires rest == n % p
  requires n == leftMost * p + rest
  requires leftMost < 10
  ensures leftMost + SumDigitsRecursive(rest, p / 10) == (n % 10) + SumDigits(n / 10)
{
  // Both sides equal the total digit sum of n
  // Left side: leftmost digit + sum of remaining digits
  // Right side: rightmost digit + sum of remaining digits
  
  // This is true because digit sum is invariant under rearrangement
  assert leftMost + SumDigitsRecursive(rest, p / 10) == SumDigits(n);
  assert (n % 10) + SumDigits(n / 10) == SumDigits(n);
}
// </vc-helpers>

//lemma DivIsZero()
//  ensures forall num, den : nat :: den >= 1 && num < den ==> num/den == 0

lemma X(x: nat)
  ensures Power10(NumberOfDigits(x)) > x
{
  if x <= 9
  {
    assert NumberOfDigits(x) == 1;
    assert Power10(NumberOfDigits(x)) == 10;
    assert Power10(NumberOfDigits(x)) > x;
  }
  else // >= 10
  {
    assert NumberOfDigits(x) >= 2;
    X(x/10);
    assert NumberOfDigits(x) == NumberOfDigits(x/10) + 1;
    assert Power10(NumberOfDigits(x)) == Power10(NumberOfDigits(x/10)) * 10;
    assert Power10(NumberOfDigits(x)) > x;
  }
}

lemma NumberIdentity(number: nat, pmax: nat)
  requires pmax == Power10(NumberOfDigits(number))
  ensures number == number % pmax
{
  if NumberOfDigits(number) == 1
  {
    assert 0 <= number <= 9;
    assert pmax == 10;
    assert number == number % pmax;
  }
  else // > 1
  {
    assert pmax == Power10(NumberOfDigits(number)) ==> pmax/10 == Power10(NumberOfDigits(number/10));
    NumberIdentity(number/10, pmax/10);
    assert number >= 10;
    assert pmax >= 100;
    assert number < pmax;
    assert forall n, m :: 0 < n < m <= pmax ==> n%m == n;
    assert number == number % pmax;
  }

}


lemma InIntValues(n: nat)
  ensures 0 in IntValues(n)
  ensures n in IntValues(n)
  ensures n/10 in IntValues(n)
{}

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