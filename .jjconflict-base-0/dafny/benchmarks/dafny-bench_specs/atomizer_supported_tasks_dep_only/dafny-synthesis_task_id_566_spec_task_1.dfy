// SPEC 
method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
{
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



//ATOM_PLACEHOLDER_InIntValues

// ghost function ValuesOfn(number: nat, ndigits: nat) : (r: seq<nat>)
// {
//   seq(ndigits+1, i requires 0 <= i <= ndigits => number / PowersOfTen[i])
// }

//ATOM_PLACEHOLDER_IntValues

// ATOM 

function Power10(n: nat): (r: nat)
  ensures r >= 1
  ensures n > 0 ==> r % 10 == 0
{
  if (n == 0) then 1 else 10 * Power10(n-1)
}


//ATOM_PLACEHOLDER_NumberToSeq

//ATOM_PLACEHOLDER_Sum

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
