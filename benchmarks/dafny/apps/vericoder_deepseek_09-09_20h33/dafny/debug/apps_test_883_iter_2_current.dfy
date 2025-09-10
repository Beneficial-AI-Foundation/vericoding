predicate ValidInput(n: int, friends: seq<int>)
{
  n >= 1 && |friends| == n && forall i :: 0 <= i < |friends| ==> 1 <= friends[i] <= 5
}

function sum_sequence(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + sum_sequence(s[1..])
}

predicate DimaCleans(n: int, friends: seq<int>, dima_fingers: int)
  requires ValidInput(n, friends)
  requires 1 <= dima_fingers <= 5
{
  var total_sum := sum_sequence(friends) + dima_fingers;
  var total_people := n + 1;
  total_sum % total_people == 1
}

function CountValidChoices(n: int, friends: seq<int>): int
  requires ValidInput(n, friends)
{
  CountValidChoicesHelper(n, friends, 1)
}

function CountValidChoicesHelper(n: int, friends: seq<int>, finger_count: int): int
  requires ValidInput(n, friends)
  requires 1 <= finger_count <= 6
  decreases 6 - finger_count
{
  if finger_count > 5 then
    0
  else if !DimaCleans(n, friends, finger_count) then
    1 + CountValidChoicesHelper(n, friends, finger_count + 1)
  else
    CountValidChoicesHelper(n, friends, finger_count + 1)
}

// <vc-helpers>
lemma CountValidChoicesHelperCorrect(n: int, friends: seq<int>, finger_count: int) returns (count: int)
  requires ValidInput(n, friends)
  requires 1 <= finger_count <= 6
  ensures count == CountValidChoicesHelper(n, friends, finger_count)
  decreases 6 - finger_count
{
  if finger_count > 5 {
    count := 0;
  } else {
    var rest := CountValidChoicesHelperCorrect(n, friends, finger_count + 1);
    if !DimaCleans(n, friends, finger_count) {
      count := 1 + rest;
    } else {
      count := rest;
    }
  }
}

ghost method CountValidChoicesHelperLemma(n: int, friends: seq<int>, i: int, j: int)
  requires ValidInput(n, friends)
  requires 1 <= i <= j <= 6
  ensures CountValidChoicesHelper(n, friends, i) == CountValidChoicesHelper(n, friends, j) + (if j < 6 then CountValidChoicesHelper(n, friends, i) - CountValidChoicesHelper(n, friends, j) else 0)
{
  if i < j {
    CountValidChoicesHelperLemma(n, friends, i, j - 1);
    CountValidChoicesHelperLemma(n, friends, j - 1, j);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, friends: seq<int>) returns (result: int)
  requires ValidInput(n, friends)
  ensures 0 <= result <= 5
  ensures result == CountValidChoices(n, friends)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 1;
  while i <= 5
    invariant 1 <= i <= 6
    invariant result == CountValidChoicesHelper(n, friends, i)
    decreases 6 - i
  {
    if !DimaCleans(n, friends, i) {
      result := result + 1;
    }
    i := i + 1;
    CountValidChoicesHelperLemma(n, friends, i, i);
  }
}
// </vc-code>

