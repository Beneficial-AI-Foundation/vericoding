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
lemma CountValidChoicesHelperCorrectness(n: int, friends: seq<int>, finger_count: int, accumulator: int)
  requires ValidInput(n, friends)
  requires 1 <= finger_count <= 6
  requires 0 <= accumulator <= finger_count - 1
  ensures CountValidChoicesHelper(n, friends, finger_count) + accumulator >= 0
  ensures CountValidChoicesHelper(n, friends, finger_count) + accumulator <= 5
  decreases 6 - finger_count
{
  if finger_count > 5 {
    assert CountValidChoicesHelper(n, friends, finger_count) == 0;
  } else {
    CountValidChoicesHelperCorrectness(n, friends, finger_count + 1, 
      if !DimaCleans(n, friends, finger_count) then accumulator + 1 else accumulator);
  }
}

lemma CountValidChoicesBounds(n: int, friends: seq<int>)
  requires ValidInput(n, friends)
  ensures 0 <= CountValidChoices(n, friends) <= 5
{
  CountValidChoicesHelperCorrectness(n, friends, 1, 0);
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
  var count := 0;
  var finger := 1;
  
  while finger <= 5
    invariant 1 <= finger <= 6
    invariant count == CountValidChoicesHelper(n, friends, 1) - CountValidChoicesHelper(n, friends, finger)
    invariant 0 <= count <= finger - 1
  {
    var total_sum := sum_sequence(friends) + finger;
    var total_people := n + 1;
    
    if total_sum % total_people != 1 {
      count := count + 1;
    }
    
    finger := finger + 1;
  }
  
  CountValidChoicesBounds(n, friends);
  result := count;
}
// </vc-code>

