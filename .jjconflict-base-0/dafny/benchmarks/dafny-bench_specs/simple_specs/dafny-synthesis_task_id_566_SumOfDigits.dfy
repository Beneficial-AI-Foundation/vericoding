//ATOM

function SumDigitsRecursive(n: nat, p: nat) : (r: nat)
{
 if n == 0 || p == 0 then 0
 else
  var leftMostDigit := n/p;
  var rest := n%p;
  leftMostDigit + SumDigitsRecursive(rest, p/10)

}


//ATOM

function SumDigits(n: nat) : nat
{
 var ndigits := NumberOfDigits(n);
 var p := Power10(ndigits-1);
 SumDigitsRecursive(n, p)
}


//ATOM

function Power10(n: nat): (r: nat)
 ensures r >= 1
 ensures n > 0 ==> r % 10 == 0
{
 if (n == 0) then 1 else 10 * Power10(n-1)
}


//ATOM

function NumberOfDigits(n: nat) : (r: nat)
 ensures r >= 1
 ensures r == 1 <==> 0 <= n <= 9
{
 if 0 <= n <= 9 then 1 else 1+NumberOfDigits(n/10)
}


// SPEC
method SumOfDigits(number: nat) returns (sum: nat)
 requires number >= 0
 ensures sum >= 0
 ensures sum == SumDigits(number)
{
}
