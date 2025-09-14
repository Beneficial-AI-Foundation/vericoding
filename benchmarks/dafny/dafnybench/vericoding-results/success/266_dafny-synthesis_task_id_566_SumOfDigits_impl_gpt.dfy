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

// </vc-helpers>

// <vc-spec>
method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
// </vc-spec>
// <vc-code>
{
  sum := SumDigits(number);
}
// </vc-code>

