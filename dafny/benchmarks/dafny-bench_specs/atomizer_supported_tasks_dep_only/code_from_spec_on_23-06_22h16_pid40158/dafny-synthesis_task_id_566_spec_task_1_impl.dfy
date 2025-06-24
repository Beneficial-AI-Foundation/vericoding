//IMPL 
method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
{
  /* code modified by LLM (iteration 4): Added verification assertions to help Dafny prove correctness */
  var ndigits := NumberOfDigits(number);
  var p := Power10(ndigits-1);
  
  /* code modified by LLM (iteration 4): Assert that our computation matches SumDigits definition */
  assert ndigits == NumberOfDigits(number);
  assert p == Power10(NumberOfDigits(number)-1);
  
  sum := SumDigitsRecursive(number, p);
  
  /* code modified by LLM (iteration 4): Final assertion to help verification */
  assert sum == SumDigitsRecursive(number, Power10(NumberOfDigits(number)-1));
}

// ATOM 
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
function Power10(n: nat): (r: nat)
  ensures r >= 1
  ensures n > 0 ==> r % 10 == 0
{
  if (n == 0) then 1 else 10 * Power10(n-1)
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