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
function CalculateCountValid(n: int, friends: seq<int>, limit: int): int
  requires ValidInput(n, friends)
  requires 1 <= limit <= 6
  ensures 0 <= CalculateCountValid(n, friends, limit) <= limit - 1
{
  var count := 0;
  var total_friends_sum := sum_sequence(friends);
  for dima_fingers := 1 to limit - 1
    invariant 0 <= count <= dima_fingers - 1
    invariant forall f :: 1 <= f < dima_fingers ==>
                  ((total_friends_sum + f) % (n + 1) != 1) == !DimaCleans(n, friends, f)
    invariant count == (calc_sum_valid_choices(n, friends, 1, dima_fingers - 1))
  {
    if !DimaCleans(n, friends, dima_fingers)
    {
      count := count + 1;
    }
  }
  return count;
}

// Lemma to establish equivalence between CountValidChoicesHelper and a summed function
ghost function calc_sum_valid_choices(n: int, friends: seq<int>, start_finger: int, end_finger: int): int
  requires ValidInput(n, friends)
  requires 1 <= start_finger <= 6
  requires start_finger <= end_finger + 1
  requires end_finger <= 5
{
  if start_finger > end_finger then
    0
  else if !DimaCleans(n, friends, start_finger) then
    1 + calc_sum_valid_choices(n, friends, start_finger + 1, end_finger)
  else
    calc_sum_valid_choices(n, friends, start_finger + 1, end_finger)
}

lemma SumValidChoicesLemma(n: int, friends: seq<int>, start_finger: int, end_finger: int)
  requires ValidInput(n, friends)
  requires 1 <= start_finger <= 6
  requires start_finger <= end_finger + 1
  requires end_finger <= 5
  ensures calc_sum_valid_choices(n, friends, start_finger, end_finger) == CountValidChoicesHelper(n, friends, start_finger) - CountValidChoicesHelper(n, friends, end_finger + 1)
  decreases 6 - start_finger
{
  if start_finger > end_finger then
    assert calc_sum_valid_choices(n, friends, start_finger, end_finger) == 0;
    assert CountValidChoicesHelper(n, friends, start_finger) == 0;
    assert CountValidChoicesHelper(n, friends, end_finger + 1) == 0;
  else if !DimaCleans(n, friends, start_finger) then
    SumValidChoicesLemma(n, friends, start_finger + 1, end_finger);
    assert calc_sum_valid_choices(n, friends, start_finger, end_finger) == 1 + calc_sum_valid_choices(n, friends, start_finger + 1, end_finger);
    assert CountValidChoicesHelper(n, friends, start_finger) == 1 + CountValidChoicesHelper(n, friends, start_finger + 1);
    assert CountValidChoicesHelper(n, friends, start_finger) - CountValidChoicesHelper(n, friends, end_finger + 1) == 1 + (CountValidChoicesHelper(n, friends, start_finger + 1) - CountValidChoicesHelper(n, friends, end_finger + 1));
  else
    SumValidChoicesLemma(n, friends, start_finger + 1, end_finger);
    assert calc_sum_valid_choices(n, friends, start_finger, end_finger) == calc_sum_valid_choices(n, friends, start_finger + 1, end_finger);
    assert CountValidChoicesHelper(n, friends, start_finger) == CountValidChoicesHelper(n, friends, start_finger + 1);
    assert CountValidChoicesHelper(n, friends, start_finger) - CountValidChoicesHelper(n, friends, end_finger + 1) == (CountValidChoicesHelper(n, friends, start_finger + 1) - CountValidChoicesHelper(n, friends, end_finger + 1));
}

lemma TrivialCountValidChoicesHelperProperty(n: int, friends: seq<int>)
  requires ValidInput(n, friends)
  ensures CountValidChoicesHelper(n, friends, 6) == 0
{
  // This is a direct consequence of the definition of CountValidChoicesHelper
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
    var total_friends_sum := sum_sequence(friends);

    // This loop calculates the number of valid choices for Dima's fingers.
    // A choice is valid if Dima's fingers (1-5) result in the total sum of fingers
    // (friends' fingers + Dima's fingers) not being congruent to 1 modulo (n+1).
    for dima_fingers := 1 to 5
      invariant 0 <= count <= dima_fingers - 1
      invariant count == CalculateCountValid(n, friends, dima_fingers)
      invariant count == calc_sum_valid_choices(n, friends, 1, dima_fingers - 1)
    {
      // Check if the current choice of Dima's fingers makes Dima clean the table.
      // DimaCleans returns true if (total_friends_sum + dima_fingers) % (n+1) == 1.
      // We want to count cases where Dima *doesn't* clean, so !DimaCleans is the condition.
      if (total_friends_sum + dima_fingers) % (n + 1) != 1
      {
        count := count + 1;
      }
    }
    
    TrivialCountValidChoicesHelperProperty(n, friends);
    SumValidChoicesLemma(n, friends, 1, 5);
    
    // The final count should be equal to CountValidChoices(n, friends)
    // which is defined as CountValidChoicesHelper(n, friends, 1).
    // From SumValidChoicesLemma, we have:
    // calc_sum_valid_choices(n, friends, 1, 5) == CountValidChoicesHelper(n, friends, 1) - CountValidChoicesHelper(n, friends, 6)
    // And we know CountValidChoicesHelper(n, friends, 6) == 0.
    // So, calc_sum_valid_choices(n, friends, 1, 5) == CountValidChoicesHelper(n, friends, 1).
    // The loop calculates count which equals calc_sum_valid_choices(n, friends, 1, 5).
    // Therefore, count must equal CountValidChoices(n, friends).
    result := count;
}
// </vc-code>

