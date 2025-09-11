// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
