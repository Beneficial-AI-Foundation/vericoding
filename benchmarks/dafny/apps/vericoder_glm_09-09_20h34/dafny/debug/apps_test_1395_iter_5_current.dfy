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
// (empty)
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  // Extract the line before the first newline
  var pos: int := 0;
  while pos < |stdin_input| && stdin_input[pos] != '\n'
  {
    pos := pos + 1;
  }
  var line := stdin_input[..pos];   // from 0 to pos (exclusive of pos)

  // Now, split line by space to get two tokens
  var spacePos: int := 0;
  while spacePos < |line| && line[spacePos] != ' '
  {
    spacePos := spacePos + 1;
  }

  if spacePos == |line| {
    // no space found, so return "0"
    return "0";
  }

  var num_str := line[..spacePos];
  var mod_str := line[spacePos+1..];

  // Check that num_str and mod_str are valid digit strings and non-empty
  if |num_str| == 0 || |mod_str| == 0 || !ValidDigitString(num_str) || !ValidDigitString(mod_str) {
    return "0";
  }

  // Parse mod_str to integer m
  var m: int := 0;
  var i: int := 0;
  while i < |mod_str|
  {
    var digit := mod_str[i] - '0';   // This is an integer value: '0'->0, '1'->1, ... '9'->9
    m := m * 10 + digit;
    i := i + 1;
  }

  // Check that m is at least 2
  if m < 2 {
    return "0";
  }

  // Now, check cyclic shifts of num_str: for each shift in [0, |num_str|-1]
  var shift: int := 0;
  while shift < |num_str|
  {
    if isGoodShift(num_str, shift) && cyclicShiftRemainder(num_str, shift, m) == 0 {
      var shifted := num_str[shift..] + num_str[..shift];
      return shifted;
    }
    shift := shift + 1;
  }

  return "0";
}
// </vc-code>

