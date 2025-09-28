function CountValidMinutes(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 then 0
    else if a == 1 && b == 1 then 0
    else (if a > 1 || b > 1 then 1 else 0) + 
         CountValidMinutes(if a < b then a + 1 else a - 2, if a < b then b - 2 else b + 1)
}

// <vc-helpers>
lemma CountValidMinutesIsNonNegative(a: int, b: int)
  requires 0 <= a && 0 <= b
  ensures CountValidMinutes(a, b) >= 0
  decreases a + b
{
  if a <= 0 || b <= 0 {
  } else if a == 1 && b == 1 {
  } else {
    var term := if a > 1 || b > 1 then 1 else 0;
    var na := if a < b then a + 1 else a - 2;
    var nb := if a < b then b - 2 else b + 1;
    if na >= 0 && nb >= 0 {
      CountValidMinutesIsNonNegative(na, nb);
    }
    assert CountValidMinutes(na, nb) >= 0;
    assert term >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a1: int, a2: int) returns (result: int)
    requires a1 >= 1 && a2 >= 1
    ensures result >= 0
    ensures result == CountValidMinutes(a1, a2)
    ensures (a1 == 1 && a2 == 1) ==> result == 0
// </vc-spec>
// <vc-code>
{
  CountValidMinutesIsNonNegative(a1, a2);
  result := CountValidMinutes(a1, a2);
}
// </vc-code>

