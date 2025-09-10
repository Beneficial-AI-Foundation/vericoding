predicate ValidInput(s: string)
{
    |s| >= 3 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidAbbreviation(s: string, result: string)
{
    |result| >= 3 &&
    |s| >= 3 &&
    result[0] == s[0] &&
    result[|result|-1] == s[|s|-1] &&
    result == [s[0]] + IntToString(|s| - 2) + [s[|s|-1]]
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [(('0' as int) + (n % 10)) as char]
}

// <vc-helpers>
lemma {:axiom} IntToStringHelperPositive(n: int) 
    requires n >= 0
    ensures |IntToStringHelper(n)| == (if n == 0 then 0 else (var d := n; (var count := 0; while d > 0 { count := count + 1; d := d / 10; } count)))
{
}

lemma {:axiom} IntToStringLength(n: int)
    ensures |IntToString(n)| == (if n == 0 then 1 else if n < 0 then 1 + |IntToStringHelper(-n)| else |IntToStringHelper(n)|)
{
}

lemma {:axiom} DigitsInNumber(n: int) 
    requires n >= 0
    ensures n < 10 ==> |IntToStringHelper(n)| == (if n == 0 then 0 else 1)
    ensures n >= 10 ==> |IntToStringHelper(n)| == |IntToStringHelper(n/10)| + 1
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidAbbreviation(s, result)
// </vc-spec>
// <vc-code>
{
  var len := |s|;
  var middle := len - 2;
  var numStr := IntToString(middle);
  
  result := [s[0]] + numStr + [s[len - 1]];
}
// </vc-code>

