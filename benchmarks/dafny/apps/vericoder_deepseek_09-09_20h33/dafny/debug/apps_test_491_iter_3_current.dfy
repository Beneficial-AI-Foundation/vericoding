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
  if s[0] == '-' then 
    if |s| == 1 then 0 
    else -StringToIntPos(s[1..])
  else StringToIntPos(s)
}

function StringToIntPos(s: seq<char>): int
  requires |s| > 0
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
  decreases s
{
  if |s| == 1 then (s[0] as int - '0' as int)
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
    assert IntToString(n) == ['-'] + IntToStringPos(-n);
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
    assert IntToStringPos(n) == [('0' as int + n) as char];
  } else {
    var prefix := n / 10;
    var lastDigit := n % 10;
    StringToIntPosOfIntToStringPos(prefix);
    assert IntToStringPos(n) == IntToStringPos(prefix) + [('0' as int + lastDigit) as char];
    calc == {
      StringToIntPos(IntToStringPos(n));
      StringToIntPos(IntToStringPos(prefix) + [('0' as int + lastDigit) as char]);
      { assert |IntToStringPos(prefix)| > 0; }
      { assert forall k :: 0 <= k < |IntToStringPos(prefix)| ==> '0' <= IntToStringPos(prefix)[k] <= '9'; }
      { assert '0' <= ('0' as int + lastDigit) as char <= '9'; }
      StringToIntPos(IntToStringPos(prefix)) * 10 + lastDigit;
      n;
    }
  }
}

lemma SubstringPreservesDigits(s: seq<char>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9' || s[k] == '-'
  ensures forall k :: 0 <= k < |s[start..end]| ==> '0' <= s[start..end][k] <= '9' || s[start..end][k] == '-'
{
}

lemma ConcatPreservesDigits(s1: seq<char>, s2: seq<char>)
  requires forall k :: 0 <= k < |s1| ==> '0' <= s1[k] <= '9' || s1[k] == '-'
  requires forall k :: 0 <= k < |s2| ==> '0' <= s2[k] <= '9' || s2[k] == '-'
  ensures forall k :: 0 <= k < |s1 + s2| ==> '0' <= (s1 + s2)[k] <= '9' || (s1 + s2)[k] == '-'
{
}

lemma IntToStringPosDigits(n: int)
  requires n > 0
  ensures forall k :: 0 <= k < |IntToStringPos(n)| ==> '0' <= IntToStringPos(n)[k] <= '9'
{
  if n < 10 {
  } else {
    IntToStringPosDigits(n / 10);
  }
}

lemma IntToStringDigits(n: int)
  requires n != 0
  ensures forall k :: 0 <= k < |IntToString(n)| ==> '0' <= IntToString(n)[k] <= '9' || IntToString(n)[k] == '-'
{
  if n < 0 {
    IntToStringPosDigits(-n);
  } else {
    IntToStringPosDigits(n);
  }
}
// </vc-helpers>
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
    IntToStringDigits(n);
    var s := IntToString(n);
    assert |s| > 0;
    assert forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9' || s[k] == '-';
    
    // option1: remove last digit
    SubstringPreservesDigits(s, 0, |s|-1);
    var option1 := StringToInt(s[..|s|-1]);
    
    // option2: remove second last digit
    var prefix := s[..|s|-2];
    var suffix := s[|s|-1..];
    SubstringPreservesDigits(s, 0, |s|-2);
    SubstringPreservesDigits(s, |s|-1, |s|);
    ConcatPreservesDigits(prefix, suffix);
    var option2 := StringToInt(prefix + suffix);
    
    if option1 > option2 {
      result := option1;
    } else {
      result := option2;
    }
  }
}
// </vc-code>

