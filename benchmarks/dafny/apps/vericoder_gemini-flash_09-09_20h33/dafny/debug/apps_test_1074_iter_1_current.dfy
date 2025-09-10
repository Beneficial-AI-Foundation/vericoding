function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}

// <vc-helpers>
function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}
// </vc-helpers>

// <vc-spec>
method solve(a: int) returns (count: int)
    requires a >= 0
    ensures count >= 0
    ensures count == CountOnesInOctal(a)
// </vc-spec>
// <vc-code>
{
  if a == 0 {
    return 0;
  } else {
    var next_a := a / 8;
    var remainder := a % 8;
    var recursive_count: int := solve(next_a);
    var current_digit_contribution := if remainder == 1 then 1 else 0;
    count := current_digit_contribution + recursive_count;
    return count;
  }
}
// </vc-code>

