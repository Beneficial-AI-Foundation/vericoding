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
function IsPrime(n: int): bool
  requires n >= 0
{
  /* helper modified by LLM (iteration 5): Corrected `return false` to be outside the loop body.*/
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else
  {
    var i := 3;
    while i * i <= n
      invariant 3 <= i <= n + 1
      invariant i % 2 == 1
      invariant forall k :: 3 <= k < i && k % 2 == 1 ==> n % k != 0
    {
      if n % i == 0 then return false;
      i := i + 2;
    }
    return true;
  }
}
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed the parsing error by removing 'invariant forall k :: 1 <= k < i && n % k == 0 ==> (k * k == n ==> countDivisors % 2 == 1) && (k * k != n ==> countDivisors % 2 == 0)'.*/
  var w, h := ParseTwoInts(dimensions);
  if !ValidDimensions(w, h) then
    return "Invalid dimensions";

  var n := w * h;
  if n == 0 then
    return "0";
  
  if IsPrime(n) then
    return "1";

  var countDivisors := 0;
  var i := 1;
  while i * i <= n
    invariant 0 <= countDivisors
    invariant 1 <= i <= n + 1
  {
    if n % i == 0 then
      if i * i == n then
        countDivisors := countDivisors + 1;
      else
        countDivisors := countDivisors + 2;
    }
    i := i + 1;
  }

  if countDivisors % 2 == 1 then
    return "1";
  else
    return "0";
}
// </vc-code>
