// <vc-preamble>
predicate ValidInput(r: int, g: int, b: int)
{
  r >= 0 && g >= 0 && b >= 0 &&
  r <= 1000000000 && g <= 1000000000 && b <= 1000000000
}

function maxBouquets(r: int, g: int, b: int): int
  requires ValidInput(r, g, b)
{
  var s0 := if r <= g && r <= b then r else if g <= b then g else b;
  var s2 := if r >= g && r >= b then r else if g >= b then g else b;
  var s1 := r + g + b - s0 - s2;

  var singleColorBouquets := s0 / 3 + s1 / 3 + s2 / 3;
  var x := s0 % 3;
  var y := s1 % 3;
  var z := s2 % 3;

  var specialBouquets := 
    (if x == 0 && y == 2 && z == 2 && s0 != 0 then 1 else 0) +
    (if y == 0 && x == 2 && z == 2 && s1 != 0 then 1 else 0) +
    (if z == 0 && x == 2 && y == 2 && s2 != 0 then 1 else 0);

  var minRemainder := if x <= y && x <= z then x else if y <= z then y else z;

  singleColorBouquets + specialBouquets + minRemainder
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(r: int, g: int, b: int) returns (result: int)
  requires ValidInput(r, g, b)
  ensures result >= 0
  ensures result <= (r + g + b) / 3
  ensures result == maxBouquets(r, g, b)
// </vc-spec>
// <vc-code>
{
  // Sort the values
  var s := [r, g, b];
  if s[0] > s[1] {
    s := [s[1], s[0], s[2]];
  }
  if s[1] > s[2] {
    s := [s[0], s[2], s[1]];
  }
  if s[0] > s[1] {
    s := [s[1], s[0], s[2]];
  }

  // Calculate single-color bouquets
  var ans := s[0] / 3 + s[1] / 3 + s[2] / 3;

  // Calculate remainders
  var x := s[0] % 3;
  var y := s[1] % 3;
  var z := s[2] % 3;

  // Special cases
  if x == 0 && y == 2 && z == 2 && s[0] != 0 {
    ans := ans + 1;
  }
  if y == 0 && x == 2 && z == 2 && s[1] != 0 {
    ans := ans + 1;
  }
  if z == 0 && x == 2 && y == 2 && s[2] != 0 {
    ans := ans + 1;
  }

  // Add mixed bouquets from remaining flowers
  var minRemainder := if x <= y && x <= z then x else if y <= z then y else z;
  ans := ans + minRemainder;

  result := ans;
}
// </vc-code>
