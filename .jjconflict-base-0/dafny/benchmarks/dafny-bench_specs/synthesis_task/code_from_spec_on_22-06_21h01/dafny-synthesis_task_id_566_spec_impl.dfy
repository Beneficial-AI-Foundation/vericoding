// IMPL
method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
{
  /* code modified by LLM (iteration 4): Added lemma call to prove SumDigits returns non-negative value */
  SumDigitsNonNegative(number);
  sum := SumDigits(number);
}

/* code modified by LLM (iteration 4): Fixed lemma to properly prove SumDigits is always non-negative */
lemma SumDigitsNonNegative(n: nat)
  ensures SumDigits(n) >= 0
{
  var ndigits := NumberOfDigits(n);
  var p := Power10(ndigits-1);
  SumDigitsRecursiveNonNegative(n, p);
}

/* code modified by LLM (iteration 4): Fixed recursive lemma with proper termination and proof structure */
lemma SumDigitsRecursiveNonNegative(n: nat, p: nat)
  ensures SumDigitsRecursive(n, p) >= 0
  decreases n, p
{
  if n == 0 || p == 0 {
    // Base case: SumDigitsRecursive returns 0
  } else {
    var leftMostDigit := n/p;
    var rest := n%p;
    // leftMostDigit is nat, so >= 0
    if p >= 10 {
      SumDigitsRecursiveNonNegative(rest, p/10);
      // Now we know SumDigitsRecursive(rest, p/10) >= 0
    }
    // The sum of two non-negative numbers is non-negative
  }
}

//lemma DivIsZero()
//  ensures forall num, den : nat :: den >= 1 && num < den ==> num/den == 0

// ATOM

//lemma DivIsZero()
//  ensures forall num, den : nat :: den >= 1 && num < den ==> num/den == 0

lemma X(x: nat)
  ensures Power10(NumberOfDigits(x)) > x
{
  if x <= 9
  {
  }
  else // >= 10
  {
    X(x/10);
  }
}


// ATOM

lemma NumberIdentity(number: nat, pmax: nat)
  requires pmax == Power10(NumberOfDigits(number))
  ensures number == number % pmax
{
  if NumberOfDigits(number) == 1
  {
  }
  else // > 1
  {
    NumberIdentity(number/10, pmax/10);
  }

}



// ATOM


lemma InIntValues(n: nat)
  ensures 0 in IntValues(n)
  ensures n in IntValues(n)
  ensures n/10 in IntValues(n)
{}


// ghost function ValuesOfn(number: nat, ndigits: nat) : (r: seq<nat>)
// {
//   seq(ndigits+1, i requires 0 <= i <= ndigits => number / PowersOfTen[i])
// }

// ATOM

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


// ATOM

function Power10(n: nat): (r: nat)
  ensures r >= 1
  ensures n > 0 ==> r % 10 == 0
{
  if (n == 0) then 1 else 10 * Power10(n-1)
}


// ATOM

function NumberToSeq(number: int) : seq<int>
  requires number >= 0
{
  if number == 0 then []
  else [number % 10] + NumberToSeq(number/10)
}


// ATOM

function Sum(digits: seq<int>) : int
{
  if |digits| == 0 then 0 else digits[0] + Sum(digits[1..])
}


// ATOM

function SumDigits(n: nat) : nat
{
  var ndigits := NumberOfDigits(n);
  var p := Power10(ndigits-1);
  SumDigitsRecursive(n, p)
}


// ATOM

function SumDigitsRecursive(n: nat, p: nat) : (r: nat)
{
  if n == 0 || p == 0 then 0
  else
    var leftMostDigit := n/p;
    var rest := n%p;
    leftMostDigit + SumDigitsRecursive(rest, p/10)

}


// ATOM

function NumberOfDigits(n: nat) : (r: nat)
  ensures r >= 1
  ensures r == 1 <==> 0 <= n <= 9
{
  if 0 <= n <= 9 then 1 else 1+NumberOfDigits(n/10)
}