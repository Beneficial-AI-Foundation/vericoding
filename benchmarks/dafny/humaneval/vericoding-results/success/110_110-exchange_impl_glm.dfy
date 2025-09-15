// <vc-preamble>
function IsEven(n: int) : bool
{
  n % 2 == 0
}
function CountEvens(lst: seq<int>): nat
{

  if |lst| == 0 then 0
  else (if IsEven(lst[0]) then 1 else 0) + CountEvens(lst[1..])

}
// </vc-preamble>

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
  /* code modified by LLM (iteration 5): added missing semicolon after YES assignment */
  var evens1 := CountEvens(lst1);
  var evens2 := CountEvens(lst2);
  var totalEvens := evens1 + evens2;
  var len1 := |lst1|;
  
  if totalEvens >= len1 {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>
