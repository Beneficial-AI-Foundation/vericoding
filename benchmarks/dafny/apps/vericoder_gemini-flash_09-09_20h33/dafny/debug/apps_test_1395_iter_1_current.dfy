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
function SplitOnNewline(s: string): (line: string, rest: string)
  requires exists pos :: 0 <= pos < |s| && s[pos] == '\n'
  ensures exists pos :: 0 <= pos < |s| && s[pos] == '\n' ==> line + "\n" + rest == s
  ensures '\n' !in line
{
  var newlinePos := 0;
  while (newlinePos < |s| && s[newlinePos] != '\n')
    invariant 0 <= newlinePos <= |s|
    invariant '\n' !in s[..newlinePos]
  {
    newlinePos := newlinePos + 1;
  }
  return s[..newlinePos], s[newlinePos+1..];
}

function StringToInt(s: string): int
  requires ValidDigitString(s)
  decreases |s|
{
  if |s| == 0 then 0
  else
    (StringToInt(s[..|s|-1]) * 10) + ((s[|s|-1] as int) - ('0' as int))
}

function Power(base: int, exp: int): int
  requires exp >= 0
  ensures Power(base, exp) >= 0
  decreases exp
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

function IntToString(n: int): string
  requires n >= 0
  ensures ValidDigitString(IntToString(n))
  ensures n == StringToInt(IntToString(n))
  decreases n
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant ValidDigitString(s)
      invariant temp == 0 ==> n == StringToInt(IntToString(n))
      invariant temp > 0 ==> n % (Power(10, |s|+1)) == StringToInt(s) + (temp % 10) * Power(10, |s|)
      invariant temp > 0 ==> StringToInt(IntToString(temp) + s) == n
    {
      var digit := temp % 10;
      s := (('0' as int) + digit as char) + s;
      temp := temp / 10;
    }
    s
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var M_str, rest := SplitOnNewline(stdin_input);
  var N_str, _ := SplitOnNewline(rest);

  if !(ValidNumberString(M_str)) || !(ValidNumberString(N_str)) then
    return "0";

  var M := StringToInt(M_str);
  var N := StringToInt(N_str);

  if M < 2 || M > 1000000000 then
    return "0";
  if N < 1 || N > 1000000000 then
    return "0";

  if N == 1 then
    return "1";

  if N == 2 then
    return "2";

  // Calculate the remainder for N-threaded process
  // The first "thread" is thread 1, which represents 0.
  // The N-threaded process corresponds to rotating the cyclic number 1 step at a time,
  // starting from the 0-th position (thread 1).
  // The cyclic number 1/M has |M|-1 digits in its repeating part.
  // The problem asks for the remainder considering the cyclic shift.
  // The cyclic remainder here is equivalent to the (N-1)th shift remainder (0-indexed).
  // E.g., for N=1, the 0-th shift, (1-1)=0-th shift.
  // For N=2, the 1st shift, (2-1)=1st shift.
  // So we calculate cyclicShiftRemainder(M_str, N-1, M).

  var shift_value := (N - 1) % M_str.Length; // Ensure shift is within bounds
  if shift_value < 0 then shift_value := shift_value + M_str.Length; // Handle negative result from % for a givendafny-compiler

  var result_int := cyclicShiftRemainder(M_str, shift_value, M);
  
  if !isGoodShift(M_str, shift_value) then
    return "0"; // M[N] == '0' condition:  M is cyclic, M_str[shift_value] corresponds to M[N]

  return IntToString(result_int);
}
// </vc-code>

