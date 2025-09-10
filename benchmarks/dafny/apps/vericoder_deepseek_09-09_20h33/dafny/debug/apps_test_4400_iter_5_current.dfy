predicate ValidInput(s: string) {
    |s| == 3 && forall i :: 0 <= i < |s| ==> s[i] == 'S' || s[i] == 'R'
}

function MaxConsecutiveRainyDays(s: string): int
    requires ValidInput(s)
{
    if s == "RRR" then 3
    else if s[0..2] == "RR" || s[1..3] == "RR" then 2
    else if 'R' in s then 1
    else 0
}

// <vc-helpers>
lemma MaxConsecutiveRainyDaysLemma(s: string, start: int, end: int)
  requires ValidInput(s)
  requires 0 <= start <= end <= 3
  ensures forall i :: start <= i < end ==> s[i] == 'R' ==> MaxConsecutiveRainyDays(s) >= end - start
{
  if end - start == 3 {
    if s == "RRR" {
      assert MaxConsecutiveRainyDays(s) == 3;
    }
  } else if end - start == 2 {
    if s[0..2] == "RR" {
      assert MaxConsecutiveRainyDays(s) >= 2;
    } else if s[1..3] == "RR" {
      assert MaxConsecutiveRainyDays(s) >= 2;
    } else {
      assert forall i :: 0 <= i < 2 ==> s[i] != 'R' || forall j :: 1 <= j < 3 ==> s[j] != 'R';
    }
  } else if end - start == 1 {
    if 'R' in s {
      assert MaxConsecutiveRainyDays(s) >= 1;
    } else {
      // Handle case where there are no 'R' in string
      assert forall i :: 0 <= i < 3 ==> s[i] != 'R';
    }
  }
}

lemma NoRainLemma(s: string)
  requires ValidInput(s)
  requires forall i :: 0 <= i < 3 ==> s[i] == 'S'
  ensures MaxConsecutiveRainyDays(s) == 0
{
  assert s == "SSS";
  assert !('R' in s);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: int)
    requires ValidInput(input)
    ensures result == MaxConsecutiveRainyDays(input)
    ensures 0 <= result <= 3
// </vc-spec>
// <vc-code>
{
  if input[0] == 'R' && input[1] == 'R' && input[2] == 'R' {
    result := 3;
  } else if (input[0] == 'R' && input[1] == 'R') || (input[1] == 'R' && input[2] == 'R') {
    result := 2;
  } else if input[0] == 'R' || input[1] == 'R' || input[2] == 'R' {
    result := 1;
  } else {
    result := 0;
  }
  assert result == MaxConsecutiveRainyDays(input) by {
    if input[0] == 'R' && input[1] == 'R' && input[2] == 'R' {
      assert input == "RRR";
      assert MaxConsecutiveRainyDays(input) == 3;
    } else if (input[0] == 'R' && input[1] == 'R') {
      assert input[0..2] == "RR";
      assert MaxConsecutiveRainyDays(input) == 2 || MaxConsecutiveRainyDays(input) == 3; // Could be RRR
    } else if (input[1] == 'R' && input[2] == 'R') {
      assert input[1..3] == "RR";
      assert MaxConsecutiveRainyDays(input) == 2 || MaxConsecutiveRainyDays(input) == 3; // Could be RRR
    } else if input[0] == 'R' || input[1] == 'R' || input[2] == 'R' {
      assert 'R' in input;
      assert MaxConsecutiveRainyDays(input) >= 1;
      if MaxConsecutiveRainyDays(input) > 1 {
        // If we get here, it must be that one of the RR cases was missed
        if input[0] == 'R' && input[1] == 'R' {
          assert false; // Contradiction - should have been caught above
        }
        if input[1] == 'R' && input[2] == 'R' {
          assert false; // Contradiction - should have been caught above
        }
        if input[0] == 'R' && input[1] == 'R' && input[2] == 'R' {
          assert false; // Contradiction - should have been caught above
        }
      }
    } else {
      assert forall i :: 0 <= i < 3 ==> input[i] == 'S';
      assert !('R' in input);
      assert MaxConsecutiveRainyDays(input) == 0;
    }
  }
}
// </vc-code>

