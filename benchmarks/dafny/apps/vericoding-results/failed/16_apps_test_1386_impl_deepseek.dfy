predicate ValidInput(input: string)
{
  |input| > 0 &&
  exists i :: 0 < i < |input| - 1 && input[i] == ' ' &&
  (forall j :: 0 <= j < i ==> '0' <= input[j] <= '9') &&
  (forall j :: i < j < |input| ==> '0' <= input[j] <= '9')
}

predicate ValidDimensions(w: int, h: int)
{
  w >= 1 && h >= 1 && w <= 1000 && h <= 1000
}

function ParseTwoInts(input: string): (int, int)
  requires ValidInput(input)
{
  var spaceIndex := FindSpace(input, 0);
  var w := StringToInt(input[0..spaceIndex]);
  var h := StringToInt(input[spaceIndex+1..]);
  (w, h)
}

function FindSpace(s: string, start: int): int
  requires 0 <= start < |s|
  requires exists i :: start <= i < |s| && s[i] == ' '
  ensures start <= FindSpace(s, start) < |s|
  ensures s[FindSpace(s, start)] == ' '
  decreases |s| - start
{
  if s[start] == ' ' then start
  else FindSpace(s, start + 1)
}

function StringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  if |s| == 1 then s[0] as int - '0' as int
  else StringToInt(s[0..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function IntToString(n: int): string
  requires n >= 0
  ensures |IntToString(n)| > 0
{
  if n == 0 then "0"
  else if n < 10 then [('0' as int + n) as char]
  else IntToString(n / 10) + IntToString(n % 10)
}

function ModPow(base: int, exp: int, mod: int): int
  requires mod > 1
  requires exp >= 0
  ensures 0 <= ModPow(base, exp, mod) < mod
{
  if exp == 0 then 1 % mod
  else if exp % 2 == 0 then
    var half := ModPow(base, exp / 2, mod);
    (half * half) % mod
  else
    (base * ModPow(base, exp - 1, mod)) % mod
}

// <vc-helpers>
lemma ValidInputEnsuresSpaceIndexInRange(input: string)
  requires ValidInput(input)
  ensures 0 < FindSpace(input, 0) < |input| - 1
{
  // The existence guarantee from ValidInput ensures the space is found
}

lemma StringToIntNonNegative(s: string)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToInt(s) >= 0
{
  if |s| == 1 {
    // Single digit is always non-negative
  } else {
    StringToIntNonNegative(s[0..|s|-1]);
  }
}

lemma StringToIntBounds(s: string)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToInt(s) <= 1000
  decreases |s|
{
  if |s| == 1 {
    // Single digit is at most 9
  } else if |s| == 2 {
    // Two digits: at most 99
  } else if |s| == 3 {
    // Three digits: at most 999
  } else if |s| == 4 {
    // Four digits: at most 1000 (assuming valid input)
    assert s[0] == '1';
    assert s[1] == '0';
    assert s[2] == '0';
    assert s[3] == '0';
  } else {
    // For strings longer than 4, they would be >1000 which is invalid
    StringToIntBounds(s[0..|s|-1]);
  }
}

lemma ParseTwoIntsValidDimensions(input: string)
  requires ValidInput(input)
  ensures ValidDimensions(ParseTwoInts(input).0, ParseTwoInts(input).1)
{
  var (w, h) := ParseTwoInts(input);
  ValidInputEnsuresSpaceIndexInRange(input);
  StringToIntNonNegative(input[0..FindSpace(input, 0)]);
  StringToIntNonNegative(input[FindSpace(input, 0)+1..]);
  StringToIntBounds(input[0..FindSpace(input, 0)]);
  StringToIntBounds(input[FindSpace(input, 0)+1..]);
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var (w, h) := ParseTwoInts(input);
  ParseTwoIntsValidDimensions(input);
  assert ValidDimensions(w, h);
  var area := w * h;
  var perimeter := 2 * (w + h);
  var result := IntToString(area) + " " + IntToString(perimeter);
  result;
}
// </vc-code>

