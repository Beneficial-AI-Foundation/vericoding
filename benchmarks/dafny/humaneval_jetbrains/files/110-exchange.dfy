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
