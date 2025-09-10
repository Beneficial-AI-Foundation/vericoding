predicate ValidInput(n: int)
{
    n >= 10 || n <= -10
}

function MaxBalanceAfterOperation(n: int): int
    requires ValidInput(n)
{
    if n >= 0 then n
    else 
        var s := IntToString(n);
        var option1 := StringToInt(s[..|s|-1]);  // delete last digit
        var option2 := StringToInt(s[..|s|-2] + s[|s|-1..]);  // delete digit before last
        if option1 > option2 then option1 else option2
}

// <vc-helpers>
function IntToString(n: int): string
  reads {}
  ensures (n == 0) ==> (IntToString(n) == "0")
  ensures (n > 0) ==> (forall k :: 0 <= k < |IntToString(n)| ==> IsDigit(IntToString(n)[k]))
  ensures (n > 0) ==> (IntToString(n)[0] != '0')
  ensures (n < 0) ==> (IntToString(n)[0] == '-')
  ensures (n < 0) ==> (IsDigit(IntToString(n)[1]))
{
  if n == 0 then "0"
  else if n > 0 then
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0;
      invariant forall k :: 0 <= k < |s| ==> IsDigit(s[k]);
      invariant (s == "" && temp == n) || (s != "" && n / (Power(10, |s|)) == temp);
      invariant (s != "" && temp == 0) ==> (StringToInt(s) == n);
    {
      s := (('0' as int) + (temp % 10)) as char + s;
      temp := temp / 10;
    }
    s
  else // n < 0
    var s := "";
    var temp := -n;
    while temp > 0
      invariant temp >= 0;
      invariant forall k :: 0 <= k < |s| ==> IsDigit(s[k]);
      invariant s == "" || (-n / (Power(10, |s|)) == temp);
      invariant (s != "" && temp == 0) ==> (StringToInt("-" + s) == n);
    {
      s := (('0' as int) + (temp % 10)) as char + s;
      temp := temp / 10;
    }
    "-" + s
}

function IsDigit(c: char): bool
{
  '0' <= c <= '9'
}

function StringToInt(s: string): int
  requires |s| > 0
  requires (s[0] == '-' && |s| > 1 && forall i :: 1 <= i < |s| ==> IsDigit(s[i])) ||
           (s[0] != '-' && forall i :: 0 <= i < |s| ==> IsDigit(s[i]) && (s[0] != '0' || |s| == 1));
{
  if s[0] == '-' then
    - StringToIntPositive(s[1..])
  else
    StringToIntPositive(s)
}

function StringToIntPositive(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
  requires s[0] != '0' || |s| == 1;
{
  var result := 0;
  var ten_power := 1;
  var i := |s| - 1;
  while i >= 0
    invariant i >= -1
    invariant result >= 0
    invariant ten_power == Power(10, |s| - 1 - i)
    invariant result == StringToIntPositiveSuffix(s[i+1..])
    invariant forall k :: i + 1 <= k < |s| ==> IsDigit(s[k]);
  {
    result := result + (s[i] as int - '0' as int) * ten_power;
    ten_power := ten_power * 10;
    i := i - 1;
  }
  result
}

function StringToIntPositiveSuffix(s: string): int
  requires forall i :: 0 <= i < |s| ==> IsDigit(s[i]);
  reads {}
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|;
        invariant res >= 0;
        invariant res == StringToIntPositive(s[..i])
        invariant forall k :: 0 <= k < i ==> IsDigit(s[k]);
    {
        res := res * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    res
}

function Power(base: int, exp: int): (result: int)
  requires exp >= 0
  ensures exp == 0 ==> result == 1;
  ensures exp > 0 ==> result == base * Power(base, exp - 1);
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxBalanceAfterOperation(n)
// </vc-spec>
// <vc-code>
{
    if n >= 0 then
        result := n;
    else
        var s := IntToString(n);
        var s_len := |s|;

        var option1_s := s[..s_len - 1]; // delete last digit
        var option1_val := StringToInt(option1_s);

        var first_part := if s_len - 2 >= 1 then s[..s_len - 2] else ""; // if original string is "-1", s_len-2 is -1. Should not index s[..-1].
        var middle_char_index := s_len - 1; // Index of the digit before last (which becomes the new last digit)
        var middle_char := s[middle_char_index];
        var option2_s := first_part + middle_char;
        var option2_val := StringToInt(option2_s);

        if option1_val > option2_val then
            result := option1_val;
        else
            result := option2_val;
}
// </vc-code>

