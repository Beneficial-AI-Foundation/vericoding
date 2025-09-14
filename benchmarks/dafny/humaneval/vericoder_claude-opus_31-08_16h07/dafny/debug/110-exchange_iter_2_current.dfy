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
lemma CountEvensAppend(lst: seq<int>, i: nat)
  requires i < |lst|
  ensures CountEvens(lst[..i+1]) == CountEvens(lst[..i]) + (if IsEven(lst[i]) then 1 else 0)
{
  assert lst[..i+1] == lst[..i] + [lst[i]];
  CountEvensConcat(lst[..i], [lst[i]]);
}

lemma CountEvensConcat(lst1: seq<int>, lst2: seq<int>)
  ensures CountEvens(lst1 + lst2) == CountEvens(lst1) + CountEvens(lst2)
{
  if |lst1| == 0 {
    assert lst1 + lst2 == lst2;
  } else {
    assert (lst1 + lst2)[0] == lst1[0];
    assert (lst1 + lst2)[1..] == lst1[1..] + lst2;
    CountEvensConcat(lst1[1..], lst2);
  }
}

method CountEvensIterative(lst: seq<int>) returns (count: nat)
  ensures count == CountEvens(lst)
{
  count := 0;
  var i := 0;
  
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant count == CountEvens(lst[..i])
  {
    var oldCount := count;
    if IsEven(lst[i]) {
      count := count + 1;
    }
    CountEvensAppend(lst, i);
    i := i + 1;
  }
  
  assert lst[..i] == lst;
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
  var evens1 := CountEvensIterative(lst1);
  var evens2 := CountEvensIterative(lst2);
  
  if evens1 + evens2 >= |lst1| {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

