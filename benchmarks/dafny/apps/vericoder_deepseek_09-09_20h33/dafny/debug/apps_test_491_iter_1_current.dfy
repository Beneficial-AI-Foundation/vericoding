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
function StringToInt(s: seq<char>): int
  requires |s| > 0
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9' || s[k] == '-'
  decreases s
{
  if |s| == 0 then 0
  else if s[0] == '-' then -StringToIntPos(s[1..])
  else StringToIntPos(s)
}

function StringToIntPos(s: seq<char>): int
  requires |s| > 0
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
  decreases s
{
  if |s| == 0 then 0
  else (s[0] as int - '0' as int) * Pow10(|s| - 1) + StringToIntPos(s[1..])
}

function Pow10(exp: int): int
  requires exp >= 0
{
  if exp == 0 then 1 else 10 * Pow10(exp - 1)
}

function IntToString(n: int): seq<char>
  requires n != 0
  decreases if n < 0 then -n else n
{
  if n < 0 then ['-'] + IntToStringPos(-n)
  else IntToStringPos(n)
}

function IntToStringPos(n: int): seq<char>
  requires n > 0
  decreases n
{
  if n < 10 then [('0' as int + n) as char]
  else IntToStringPos(n / 10) + [('0' as int + n % 10) as char]
}

lemma StringToIntOfIntToString(n: int)
  requires n != 0
  ensures StringToInt(IntToString(n)) == n
{
  if n < 0 {
    StringToIntPosOfIntToStringPos(-n);
  } else {
    StringToIntPosOfIntToStringPos(n);
  }
}

lemma StringToIntPosOfIntToStringPos(n: int)
  requires n > 0
  ensures StringToIntPos(IntToStringPos(n)) == n
{
  if n < 10 {
  } else {
    StringToIntPosOfIntToStringPos(n / 10);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxBalanceAfterOperation(n)
// </vc-spec>
// <vc-code>
{
  if n >= 0 {
    result := n;
  } else {
    var s := IntToString(n);
    var last := s[|s|-1];
    var secondLast := s[|s|-2];
    var option1 := StringToInt(s[..|s|-1]);
    var option2Str := s[..|s|-2] + [last];
    var option2 := StringToInt(option2Str);
    
    if option1 > option2 {
      result := option1;
    } else {
      result := option2;
    }
  }
}
// </vc-code>

