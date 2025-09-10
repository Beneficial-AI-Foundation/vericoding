predicate ValidInput(a: int, b: int)
{
  a >= 1 && b >= 1
}

function MaxDifferentDays(a: int, b: int): int
{
  if a < b then a else b
}

function RemainingAfterDifferent(a: int, b: int): int
{
  if a > b then a - MaxDifferentDays(a, b) else b - MaxDifferentDays(a, b)
}

function SameDays(a: int, b: int): int
{
  RemainingAfterDifferent(a, b) / 2
}

// <vc-helpers>
lemma MaxDifferentDaysLemma(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures MaxDifferentDays(a, b) >= 0
  ensures MaxDifferentDays(a, b) <= a
  ensures MaxDifferentDays(a, b) <= b
{
  if a < b {
    calc {
      MaxDifferentDays(a, b);
      a;
    }
  } else {
    calc {
      MaxDifferentDays(a, b);
      b;
    }
  }
}

lemma RemainingAfterDifferentLemma(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures RemainingAfterDifferent(a, b) >= 0
{
  MaxDifferentDaysLemma(a, b);
  if a > b {
    calc {
      RemainingAfterDifferent(a, b);
      a - MaxDifferentDays(a, b);
    }
  } else {
    calc {
      RemainingAfterDifferent(a, b);
      b - MaxDifferentDays(a, b);
    }
  }
}

lemma SameDaysLemma(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures SameDays(a, b) >= 0
{
  RemainingAfterDifferentLemma(a,b);
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (days_different: int, days_same: int)
  requires ValidInput(a, b)
  ensures days_different == MaxDifferentDays(a, b)
  ensures days_same == SameDays(a, b)
  ensures days_different >= 0
  ensures days_same >= 0
  ensures days_different <= a && days_different <= b
// </vc-spec>
// <vc-code>
{
  days_different := MaxDifferentDays(a, b);
  days_same := SameDays(a, b);

  MaxDifferentDaysLemma(a, b);
  SameDaysLemma(a, b);
}
// </vc-code>

