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
lemma CountValidChoicesHelperBound(n: int, friends: seq<int>, finger_count: int)
  requires ValidInput(n, friends)
  requires 1 <= finger_count <= 6
  ensures 0 <= CountValidChoicesHelper(n, friends, finger_count) <= 6 - finger_count
  decreases 6 - finger_count
{
  if finger_count > 5 {
    // By definition, when finger_count > 5 the helper returns 0
    assert CountValidChoicesHelper(n, friends, finger_count) == 0;
    assert 0 <= CountValidChoicesHelper(n, friends, finger_count) <= 6 - finger_count;
  } else {
    CountValidChoicesHelperBound(n, friends, finger_count + 1);
    var rec := CountValidChoicesHelper(n, friends, finger_count + 1);
    if !DimaCleans(n, friends, finger_count) {
      assert CountValidChoicesHelper(n, friends, finger_count) == 1 + rec;
      // rec satisfies 0 <= rec <= 6 - (finger_count + 1)
      assert 0 <= rec <= 6 - (finger_count + 1);
      assert 0 <= 1 + rec <= 6 - finger_count;
    } else {
      assert CountValidChoicesHelper(n, friends, finger_count) == rec;
      assert 0 <= rec <= 6 - (finger_count + 1);
      assert 0 <= rec <= 6 - finger_count;
    }
  }
}

lemma CountChoicesBounds(n: int, friends: seq<int>)
  requires ValidInput(n, friends)
  ensures 0 <= CountValidChoices(n, friends) <= 5
{
  CountValidChoicesHelperBound(n, friends, 1);
  assert CountValidChoices(n, friends) == CountValidChoicesHelper(n, friends, 1);
  assert 0 <= CountValidChoices(n, friends) <= 5;
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
  result := CountValidChoices(n, friends);
  CountChoicesBounds(n, friends);
}
// </vc-code>

