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
lemma HelperStep(n: int, friends: seq<int>, finger_count: int)
  requires ValidInput(n, friends)
  requires 1 <= finger_count <= 5
  ensures CountValidChoicesHelper(n, friends, finger_count) ==
            (if !DimaCleans(n, friends, finger_count) then 1 else 0) +
            CountValidChoicesHelper(n, friends, finger_count + 1)
{
  if !DimaCleans(n, friends, finger_count) {
    assert CountValidChoicesHelper(n, friends, finger_count) ==
      (if finger_count > 5 then 0
       else if !DimaCleans(n, friends, finger_count)
       then 1 + CountValidChoicesHelper(n, friends, finger_count + 1)
       else CountValidChoicesHelper(n, friends, finger_count + 1));
    assert finger_count <= 5;
    assert CountValidChoicesHelper(n, friends, finger_count) ==
      1 + CountValidChoicesHelper(n, friends, finger_count + 1);
  } else {
    assert CountValidChoicesHelper(n, friends, finger_count) ==
      (if finger_count > 5 then 0
       else if !DimaCleans(n, friends, finger_count)
       then 1 + CountValidChoicesHelper(n, friends, finger_count + 1)
       else CountValidChoicesHelper(n, friends, finger_count + 1));
    assert finger_count <= 5;
    assert CountValidChoicesHelper(n, friends, finger_count) ==
      CountValidChoicesHelper(n, friends, finger_count + 1);
  }
}

lemma HelperBase(n: int, friends: seq<int>)
  requires ValidInput(n, friends)
  ensures CountValidChoicesHelper(n, friends, 6) == 0
{
  assert CountValidChoicesHelper(n, friends, 6) ==
    (if 6 > 5 then 0
     else if !DimaCleans(n, friends, 6)
     then 1 + CountValidChoicesHelper(n, friends, 7)
     else CountValidChoicesHelper(n, friends, 7));
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
  var finger := 1;
  var res := 0;

  assert CountValidChoices(n, friends) == CountValidChoicesHelper(n, friends, 1);

  while finger <= 5
    invariant ValidInput(n, friends)
    invariant 1 <= finger <= 6
    invariant 0 <= res <= finger - 1
    invariant res + CountValidChoicesHelper(n, friends, finger) == CountValidChoices(n, friends)
    decreases 6 - finger
  {
    var c := !DimaCleans(n, friends, finger);
    HelperStep(n, friends, finger);

    if c {
      res := res + 1;
      assert res <= finger;
    } else {
      assert res <= finger - 1;
    }

    // Use the step relation to maintain the main invariant for the next iteration
    assert CountValidChoicesHelper(n, friends, finger) ==
             (if c then 1 else 0) + CountValidChoicesHelper(n, friends, finger + 1);
    if c {
      assert res + CountValidChoicesHelper(n, friends, finger + 1) ==
             (res - 1) + 1 + CountValidChoicesHelper(n, friends, finger + 1);
    } else {
      assert res + CountValidChoicesHelper(n, friends, finger + 1) ==
             res + 0 + CountValidChoicesHelper(n, friends, finger + 1);
    }

    finger := finger + 1;
  }

  assert finger == 6;
  HelperBase(n, friends);
  assert CountValidChoicesHelper(n, friends, finger) == 0;
  result := res;
}
// </vc-code>

