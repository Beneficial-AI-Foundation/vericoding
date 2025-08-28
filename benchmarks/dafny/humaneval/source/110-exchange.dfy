function IsEven(n: int) : bool
{
  n % 2 == 0
}
// pure-end
function CountEvens(lst: seq<int>): nat
{
  // impl-start
  if |lst| == 0 then 0
  else (if IsEven(lst[0]) then 1 else 0) + CountEvens(lst[1..])
  // impl-end
}
// pure-end
method Exchange(lst1: seq<int>, lst2: seq<int>) returns (result: string)
  // pre-conditions-start
  requires |lst1| > 0 && |lst2| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == "YES" || result == "NO"
  ensures result == "YES" ==> CountEvens(lst1) + CountEvens(lst2) >= |lst1|
  ensures result == "NO" ==> CountEvens(lst1) + CountEvens(lst2) < |lst1|
  // post-conditions-end
{
  // impl-start
  var totalEvens := CountEvens(lst1) + CountEvens(lst2);
  if totalEvens >= |lst1| {
    result := "YES";
  } else {
    result := "NO";
  }
  // impl-end
}
