```vc-helpers
ghost method lemma_select_at_most_two_digits_in_bounds(arr: seq<int>)
  requires |arr| >= 0 && |arr| <= 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> 0 <= select_at_most_two_digits_rec(arr)[i] < 100
  decreases |arr|
{
  if |arr| == 0 {
  } else {
    lemma_select_at_most_two_digits_in_bounds(arr[1..]);
    if 0 <= arr[0] < 100 {
      assert select_at_most_two_digits_rec(arr) == [arr[0]] + select_at_most_two_digits_rec(arr[1..]);
      assert |select_at_most_two_digits_rec(arr)| == 1 + |select_at_most_two_digits_rec(arr[1..])|;
      forall i | 0 <= i < |select_at_most_two_digits_rec(arr)|
        ensures 0 <= select_at_most_two_digits_rec(arr)[i] < 100
      {
        if i == 0 {
          assert select_at_most_two_digits_rec(arr)[0] == arr[0];
        } else {
          assert 0 <= i - 1;
          assert i - 1 < |select_at_most_two_digits_rec(arr[1..])|;
          assert select_at_most_two_digits_rec(arr)[i] == select_at_most_two_digits_rec(arr[1..])[i - 1];
        }
      }
    } else {
      assert select_at_most_two_digits_rec(arr) == select_at_most_two_digits_rec(arr[1..]);
    }
  }
}

ghost method lemma_select_at_most_two_digits_membership(arr: seq<int>)
  requires |arr| >= 0 && |arr| <= 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> select_at_most_two_digits_rec(arr)[i] in arr
  decreases |arr|
{
  if |arr