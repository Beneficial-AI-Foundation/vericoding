// <vc-preamble>
predicate IsValidIntegerInput(s: string)
{
  |s| > 0 && 
  (forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1' || s[i] == '2' || s[i] == '3' || s[i] == '4' || 
                                s[i] == '5' || s[i] == '6' || s[i] == '7' || s[i] == '8' || s[i] == '9') &&
  (|s| == 1 || s[0] != '0')
}

function StringToIntValue(s: string): int
  requires IsValidIntegerInput(s)
  ensures StringToIntValue(s) >= 0
{
  if |s| == 0 then 0
  else if |s| == 1 then
    if s[0] == '0' then 0
    else if s[0] == '1' then 1
    else if s[0] == '2' then 2
    else if s[0] == '3' then 3
    else if s[0] == '4' then 4
    else if s[0] == '5' then 5
    else if s[0] == '6' then 6
    else if s[0] == '7' then 7
    else if s[0] == '8' then 8
    else 9
  else
    StringToIntValue(s[..|s|-1]) * 10 + StringToIntValue(s[|s|-1..])
}

function StringToInt(s: string): int
  requires IsValidIntegerInput(s)
  requires StringToIntValue(s) >= 1 && StringToIntValue(s) <= 1000000
  ensures StringToInt(s) == StringToIntValue(s)
  ensures StringToInt(s) >= 1 && StringToInt(s) <= 1000000
{
  StringToIntValue(s)
}

function IntToString(n: int): string
  requires n >= 0
  ensures |IntToString(n)| > 0
  decreases n
{
  if n == 0 then "0"
  else if n < 10 then
    if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else "9"
  else
    IntToString(n / 10) + IntToString(n % 10)
}

function ModPow(base: int, exp: int, mod: int): int
  requires base >= 0 && exp >= 0 && mod > 0
  ensures ModPow(base, exp, mod) >= 0 && ModPow(base, exp, mod) < mod
  decreases exp
{
  if mod == 1 then 0
  else if exp == 0 then 1 % mod
  else if exp == 1 then base % mod
  else if exp % 2 == 0 then
    var half := ModPow(base, exp / 2, mod);
    (half * half) % mod
  else
    (base * ModPow(base, exp - 1, mod)) % mod
}
// </vc-preamble>

// <vc-helpers>
method ModPowMethod(base: int, exp: int, mod: int) returns (result: int)
  requires base >= 0 && exp >= 0 && mod > 0
  ensures result >= 0 && result < mod
  ensures result == ModPow(base, exp, mod)
{
  if mod == 1 {
    result := 0;
  } else if exp == 0 {
    result := 1 % mod;
  } else {
    var b := base % mod;
    var e := exp;
    var res := 1;

    while e > 0
      invariant e >= 0
      invariant res >= 0 && res < mod
      invariant b >= 0 && b < mod
      invariant res * ModPow(b, e, mod) % mod == ModPow(base, exp, mod)
    {
      if e % 2 == 1 {
        res := (res * b) % mod;
      }
      b := (b * b) % mod;
      e := e / 2;
    }

    result := res;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires IsValidIntegerInput(stdin_input)
  requires StringToIntValue(stdin_input) >= 1 && StringToIntValue(stdin_input) <= 1000000
  ensures |result| > 0
  ensures exists n :: 1 <= n <= 1000000 && n == StringToIntValue(stdin_input) &&
    result == IntToString((ModPow(10, n, 1000000007) - 2 * ModPow(9, n, 1000000007) + ModPow(8, n, 1000000007) + 1000000007) % 1000000007) + "\n"
// </vc-spec>
// <vc-code>
{
  var n := StringToInt(stdin_input);

  var mod := 1000000007;

  var pow10 := ModPowMethod(10, n, mod);
  var pow9 := ModPowMethod(9, n, mod);
  var pow8 := ModPowMethod(8, n, mod);

  var ans := pow10 - 2 * pow9 + pow8;
  ans := ((ans % mod) + mod) % mod;

  result := IntToString(ans) + "\n";
}
// </vc-code>
