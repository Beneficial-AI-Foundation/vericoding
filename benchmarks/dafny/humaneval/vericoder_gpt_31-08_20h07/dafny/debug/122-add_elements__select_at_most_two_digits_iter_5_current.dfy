function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function select_at_most_two_digits_rec(arr: seq<int>): seq<int>
  requires |arr| >= 0 && |arr| <= 100
{
  if |arr| == 0 then []
  else if 0 <= arr[0] < 100 then [arr[0]] + select_at_most_two_digits_rec(arr[1..])
  else select_at_most_two_digits_rec(arr[1..])
}

// <vc-helpers>
lemma TailMembership(arr: seq<int>, x: int)
  requires |arr| > 0
  ensures x in arr[1..] ==> x in arr
{
  if x in arr[1..] {
    var i :| 0 <= i < |arr[1..]| && arr[1..][i] == x;
    assert |arr[1..]| == |arr| - 1;
    assert 0 <= i < |arr| - 1;
    assert 0 <= i + 1 < |arr|;
    assert arr[1..][i] == arr[i + 1];
    var j := i + 1;
    assert 0 <= j < |arr|;
    assert arr[j] == x;
    assert x in arr;
  }
}

lemma Lemma_SelectAtMostTwoDigits_Props(arr: seq<int>)
  requires |arr| <= 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> 0 <= select_at_most_two_digits_rec(arr)[i] < 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> select_at_most_two_digits_rec(arr)[i] in arr
  decreases |arr|
{
  if |arr| == 0 {
  } else {
    assert |arr[1..]| == |arr| - 1;
    assert |arr[1..]| <= |arr|;
    assert |arr| <= 100;
    assert |arr[1..]| <= 100;
    Lemma_SelectAtMostTwoDigits_Props(arr[1..]);
    if 0 <= arr[0] < 100 {
      assert select_at_most_two_digits_rec(arr) == [arr[0]] + select_at_most_two_digits_rec(arr[1..]);
      forall i | 0 <= i < |select_at_most_two_digits_rec(arr)|
        ensures 0 <= select_at_most_two_digits_rec(arr)[i] < 100
      {
        if i == 0 {
          assert select_at_most_two_digits_rec(arr)[0] == arr[0];
        } else {
          var j := i - 1;
          assert 0 < i;
          assert 0 <= j;
          assert |select_at_most_two_digits_rec(arr)| == 1 + |select_at_most_two_digits_rec(arr[1..])|;
          assert j < |select_at_most_two_digits_rec(arr[1..])|;
          assert select_at_most_two_digits_rec(arr)[i] == select_at_most_two_digits_rec(arr[1..])[j];
        }
      }
      forall i | 0 <= i < |select_at_most_two_digits_rec(arr)|
        ensures select_at_most_two_digits_rec(arr)[i] in arr
      {
        if i == 0 {
          assert |arr| > 0;
          assert select_at_most_two_digits_rec(arr)[0] == arr[0];
          assert 0 <= 0 < |arr|;
          assert arr[0] in arr;
        } else {
          var j := i - 1;
          assert |select_at_most_two_digits_rec(arr)| == 1 + |select_at_most_two_digits_rec(arr[1..])|;
          assert 0 <= j < |select_at_most_two_digits_rec(arr[1..])|;
          assert select_at_most_two_digits_rec(arr)[i] == select_at_most_two_digits_rec(arr[1..])[j];
          assert select_at_most_two_digits_rec(arr[1..])[j] in arr[1..];
          assert |arr| > 0;
          TailMembership(arr, select_at_most_two_digits_rec(arr)[i]);
        }
      }
    } else {
      assert select_at_most_two_digits_rec(arr) == select_at_most_two_digits_rec(arr[1..]);
      forall i | 0 <= i < |select_at_most_two_digits_rec(arr)|
        ensures 0 <= select_at_most_two_digits_rec(arr)[i] < 100
      {
        assert |select_at_most_two_digits_rec(arr)| == |select_at_most_two_digits_rec(arr[1..])|;
        assert select_at_most_two_digits_rec(arr)[i] == select_at_most_two_digits_rec(arr[1..])[i];
      }
      forall i | 0 <= i < |select_at_most_two_digits_rec(arr)|
        ensures select_at_most_two_digits_rec(arr)[i] in arr
      {
        assert |arr| > 0;
        assert |select_at_most_two_digits_rec(arr)| == |select_at_most_two_digits_rec(arr[1..])|;
        assert select_at_most_two_digits_rec(arr)[i] == select_at_most_two_digits_rec(arr[1..])[i];
        assert select_at_most_two_digits_rec(arr[1..])[i] in arr[1..];
        TailMembership(arr, select_at_most_two_digits_rec(arr)[i]);
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method select_at_most_two_digits(arr: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |arr| > 0 && |arr| <= 100
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] < 100
  ensures forall i :: 0 <= i < |result| ==> result[i] in arr
  ensures result == select_at_most_two_digits_rec(arr)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := select_at_most_two_digits_rec(arr);
  Lemma_SelectAtMostTwoDigits_Props(arr);
}
// </vc-code>

method SumElementsWithAtMostTwoDigits(arr: seq<int>, k: int) returns (s: int)
  // pre-conditions-start
  requires |arr| > 0 && |arr| <= 100
  requires 1 <= k <= |arr|
  // pre-conditions-end
  // post-conditions-start
  ensures var two_digits := select_at_most_two_digits_rec(arr[..k]);
          s == sum(two_digits)
  // post-conditions-end
{
  assume{:axiom} false;
}