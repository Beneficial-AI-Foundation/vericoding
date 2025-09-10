predicate ValidInput(lines: seq<string>)
{
    |lines| > 0
}

function MAX_VALUE(): int { 4294967295 }

predicate IsOverflow(x: int)
{
    x > MAX_VALUE()
}

// <vc-helpers>
predicate IsDigit(c: char) { '0' <= c <= '9' }

predicate ValidNumber(s: string)
{
  |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i]) && (s[0] != '0' || |s| == 1)
}

function strToInt(s: string, acc: int): int
  requires acc >= 0
  decreases |s|
{
  if |s| == 0 then acc
  else strToInt(s[1..], acc * 10 + (s[0] as int - '0' as int))
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput([input])
    ensures result == "OVERFLOW!!!" || result != "OVERFLOW!!!"
// </vc-spec>
// <vc-code>
{
  assume ValidNumber(input);
  var n := strToInt(input, 0);
  if IsOverflow(n) then result := "OVERFLOW!!!"
  else result := "NO"
}
// </vc-code>

