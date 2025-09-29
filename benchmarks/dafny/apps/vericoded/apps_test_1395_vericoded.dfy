predicate ValidInput(stdin_input: string)
{
  |stdin_input| > 0 && exists pos :: 0 <= pos < |stdin_input| && stdin_input[pos] == '\n'
}

predicate ValidDigitString(s: string)
{
  |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate ValidNumberString(s: string)
{
  ValidDigitString(s) && s[0] != '0'
}

predicate ValidOutput(result: string)
{
  |result| > 0 && forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
}

function isGoodShift(s: string, shift: int): bool
  requires 0 <= shift < |s|
  requires |s| > 0
{
  s[shift] != '0'
}

function cyclicShiftRemainder(s: string, shift: int, m: int): int
  requires 0 <= shift < |s|
  requires |s| > 0
  requires m >= 2
  requires ValidDigitString(s)
  ensures 0 <= cyclicShiftRemainder(s, shift, m) < m
{
  cyclicShiftRemainderHelper(s, shift, m, 0, 0)
}

function cyclicShiftRemainderHelper(s: string, shift: int, m: int, pos: int, acc: int): int
  requires 0 <= shift < |s|
  requires |s| > 0
  requires m >= 2
  requires 0 <= pos <= |s|
  requires 0 <= acc < m
  requires ValidDigitString(s)
  ensures 0 <= cyclicShiftRemainderHelper(s, shift, m, pos, acc) < m
  decreases |s| - pos
{
  if pos == |s| then acc
  else
    var idx := (shift + pos) % |s|;
    var digit := (s[idx] as int) - ('0' as int);
    var newAcc := (acc * 10 + digit) % m;
    cyclicShiftRemainderHelper(s, shift, m, pos + 1, newAcc)
}

// <vc-helpers>
function parseInt(s: string): int
  requires ValidDigitString(s)
  ensures parseInt(s) >= 0
{
  if |s| == 0 then 0
  else if |s| == 1 then (s[0] as int) - ('0' as int)
  else parseInt(s[..|s|-1]) * 10 + (s[|s|-1] as int) - ('0' as int)
}

function intToString(n: int): string
  requires n >= 0
  ensures ValidDigitString(intToString(n))
  ensures |intToString(n)| > 0
  ensures parseInt(intToString(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n < 10 then [('0' as char) + (n as char)]
  else intToString(n / 10) + [('0' as char) + ((n % 10) as char)]
}

lemma IntToStringValid(n: int)
  requires n >= 0
  ensures ValidOutput(intToString(n))
{
  assert ValidDigitString(intToString(n));
  assert |intToString(n)| > 0;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  // Find the position of the newline
  var newlinePos := 0;
  while newlinePos < |stdin_input| && stdin_input[newlinePos] != '\n'
    invariant 0 <= newlinePos <= |stdin_input|
    invariant forall i :: 0 <= i < newlinePos ==> stdin_input[i] != '\n'
  {
    newlinePos := newlinePos + 1;
  }
  
  // Extract the number string before the newline
  if newlinePos == 0 || newlinePos >= |stdin_input| {
    return "0";
  }
  
  var numStr := stdin_input[..newlinePos];
  
  // Check if it's a valid digit string
  var isValid := true;
  var i := 0;
  while i < |numStr|
    invariant 0 <= i <= |numStr|
    invariant isValid ==> forall j :: 0 <= j < i ==> '0' <= numStr[j] <= '9'
  {
    if numStr[i] < '0' || numStr[i] > '9' {
      isValid := false;
    }
    i := i + 1;
  }
  
  if !isValid || |numStr| == 0 {
    return "0";
  }
  
  // Count the number of good shifts that give remainder 0 when divided by 11
  var count := 0;
  var shift := 0;
  
  while shift < |numStr|
    invariant 0 <= shift <= |numStr|
    invariant 0 <= count
  {
    if isGoodShift(numStr, shift) {
      var rem := cyclicShiftRemainder(numStr, shift, 11);
      if rem == 0 {
        count := count + 1;
      }
    }
    shift := shift + 1;
  }
  
  IntToStringValid(count);
  result := intToString(count);
}
// </vc-code>

