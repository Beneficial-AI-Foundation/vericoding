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
lemma modulusPreservationLemma(s: string, shift: int, pos: int, acc: int, m: int, d: int)
  requires 0 <= shift < |s|
  requires |s| > 0
  requires m >= 2
  requires 0 <= pos <= |s|
  requires 0 <= acc < m
  requires ValidDigitString(s)
  requires 0 <= d <= 9
  ensures (acc * 10 + d) % m == ((acc % m) * 10 + d) % m
{
}

predicate isLexSmallest(s: string, shift: int)
  requires 0 <= shift < |s|
  requires |s| > 0 && ValidDigitString(s)
{
  forall s2_shift :: 0 <= s2_shift < |s| && isGoodShift(s, s2_shift) ==>
            (shift == s2_shift || (exists k :: 0 <= k < |s| ==> 
            s[(shift + k) % |s|] < s[(s2_shift + k) % |s|]))
}

ghost method computeAllRemainders(s: string, m: int) returns (remainders: seq<int>)
  requires |s| > 0
  requires m >= 2
  requires ValidDigitString(s)
  ensures |remainders| == |s|
  ensures forall shift :: 0 <= shift < |s| ==> remainders[shift] == cyclicShiftRemainder(s, shift, m)
{
  remainders := [];
  var shift := 0;
  while shift < |s|
    invariant 0 <= shift <= |s|
    invariant |remainders| == shift
    invariant forall i :: 0 <= i < shift ==> remainders[i] == cyclicShiftRemainder(s, i, m)
  {
    remainders := remainders + [cyclicShiftRemainder(s, shift, m)];
    shift := shift + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var input_without_newline := stdin_input[0..(|stdin_input| - 1)];
  
  var n := |input_without_newline|;
  var best_shift := -1;
  
  var shift := 0;
  ghost var remainders := computeAllRemainders(input_without_newline, 3);
  
  while shift < n
    invariant 0 <= shift <= n
    invariant best_shift == -1 || (best_shift < n && isGoodShift(input_without_newline, best_shift) && 
              remainders[best_shift] % 3 == 0)
    invariant best_shift == -1 || isLexSmallest(input_without_newline, best_shift)
  {
    if isGoodShift(input_without_newline, shift) && remainders[shift] % 3 == 0 {
      var candidate_better := false;
      if best_shift == -1 {
        candidate_better := true;
      } else {
        var k := 0;
        while k < n && input_without_newline[(best_shift + k) % n] == input_without_newline[(shift + k) % n]
          invariant 0 <= k <= n
          invariant forall j :: 0 <= j < k ==> input_without_newline[(best_shift + j) % n] == input_without_newline[(shift + j) % n]
        {
          k := k + 1;
        }
        if k < n && input_without_newline[(best_shift + k) % n] > input_without_newline[(shift + k) % n] {
          candidate_better := true;
        }
      }
      if candidate_better {
        ghost var old_best := best_shift;
        best_shift := shift;
      }
    }
    shift := shift + 1;
  }
  
  if best_shift != -1 {
    result := "";
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |result| == i
      invariant result == (input_without_newline[best_shift..n] + input_without_newline[0..best_shift])[0..i]
    {
      result := result + [input_without_newline[(best_shift + i) % n]];
      i := i + 1;
    }
  } else {
    result := "0";
  }
}
// </vc-code>

