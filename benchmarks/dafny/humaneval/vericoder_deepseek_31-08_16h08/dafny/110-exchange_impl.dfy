function IsEven(n: int) : bool
{
  n % 2 == 0
}
function CountEvens(lst: seq<int>): nat
{
  // impl-start
  if |lst| == 0 then 0
  else (if IsEven(lst[0]) then 1 else 0) + CountEvens(lst[1..])
  // impl-end
}

// <vc-helpers>
lemma CountEvensNonNegative(lst: seq<int>)
  ensures CountEvens(lst) >= 0
{
  // The function CountEvens already returns nat which is >= 0
}

lemma CountEvensMonotonic(lst1: seq<int>, lst2: seq<int>)
  requires |lst1| == |lst2|
  requires forall i :: 0 <= i < |lst1| ==> (IsEven(lst1[i]) ==> IsEven(lst2[i]))
  ensures CountEvens(lst1) <= CountEvens(lst2)
{
  if |lst1| == 0 {
  } else {
    if IsEven(lst1[0]) {
      assert IsEven(lst2[0]);
    }
    CountEvensMonotonic(lst1[1..], lst2[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method Exchange(lst1: seq<int>, lst2: seq<int>) returns (result: string)
  // pre-conditions-start
  requires |lst1| > 0 && |lst2| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == "YES" || result == "NO"
  ensures result == "YES" ==> CountEvens(lst1) + CountEvens(lst2) >= |lst1|
  ensures result == "NO" ==> CountEvens(lst1) + CountEvens(lst2) < |lst1|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var count1 := CountEvens(lst1);
  var count2 := CountEvens(lst2);
  var total := count1 + count2;
  
  if total >= |lst1| {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

