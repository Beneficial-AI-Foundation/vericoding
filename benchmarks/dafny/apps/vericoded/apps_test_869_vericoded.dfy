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
lemma MaxDifferentDaysProperties(a: int, b: int)
  requires ValidInput(a, b)
  ensures MaxDifferentDays(a, b) >= 0
  ensures MaxDifferentDays(a, b) <= a
  ensures MaxDifferentDays(a, b) <= b
  ensures MaxDifferentDays(a, b) == if a < b then a else b
{
  // Proof is automatic from the definition
}

lemma SameDaysProperties(a: int, b: int)
  requires ValidInput(a, b)
  ensures SameDays(a, b) >= 0
{
  // The remaining items after different days is non-negative
  // and dividing by 2 maintains non-negativity
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
  days_different := if a < b then a else b;
  
  var remaining := if a > b then a - days_different else b - days_different;
  days_same := remaining / 2;
  
  // Verify the properties
  MaxDifferentDaysProperties(a, b);
  SameDaysProperties(a, b);
}
// </vc-code>

