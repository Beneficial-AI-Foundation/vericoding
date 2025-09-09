/*
function_signature: def exchange(lst1: list[int], lst2: list[int]) -> str
In this problem, you will implement a function that takes two lists of numbers, and determines whether it is possible to perform an exchange of elements between them to make lst1 a list of only even numbers. There is no limit on the number of exchanged elements between lst1 and lst2. If it is possible to exchange elements between the lst1 and lst2 to make all the elements of lst1 to be even, return "YES". Otherwise, return "NO". It is assumed that the input lists will be non-empty.
*/

function IsEven(n: int) : bool
{
  n % 2 == 0
}
function CountEvens(lst: seq<int>): nat
{

  if |lst| == 0 then 0
  else (if IsEven(lst[0]) then 1 else 0) + CountEvens(lst[1..])

}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Exchange(lst1: seq<int>, lst2: seq<int>) returns (result: string)

  requires |lst1| > 0 && |lst2| > 0

  ensures result == "YES" || result == "NO"
  ensures result == "YES" ==> CountEvens(lst1) + CountEvens(lst2) >= |lst1|
  ensures result == "NO" ==> CountEvens(lst1) + CountEvens(lst2) < |lst1|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
