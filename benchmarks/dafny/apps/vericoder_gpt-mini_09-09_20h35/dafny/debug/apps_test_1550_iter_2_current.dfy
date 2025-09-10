predicate ValidInput(n: int, digits: string)
{
    n > 0 && |digits| == n && forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
}

function modifyString(s: string, index: int): string
    requires 0 <= index < |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures |modifyString(s, index)| == |s|
    ensures forall i :: 0 <= i < |modifyString(s, index)| ==> '0' <= modifyString(s, index)[i] <= '9'
{
    var key := if s[index] == '0' then 0 else 10 - (s[index] as int - '0' as int);
    var transformed := transformDigits(s, key);
    rotateString(transformed, index)
}

function transformDigits(s: string, key: int): string
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires 0 <= key <= 9
    ensures |transformDigits(s, key)| == |s|
    ensures forall i :: 0 <= i < |transformDigits(s, key)| ==> '0' <= transformDigits(s, key)[i] <= '9'
    decreases |s|
{
    if |s| == 0 then ""
    else 
        var digit := (s[0] as int - '0' as int + key) % 10;
        [('0' as int + digit) as char] + transformDigits(s[1..], key)
}

function rotateString(s: string, index: int): string
    requires 0 <= index < |s|
    ensures |rotateString(s, index)| == |s|
{
    if |s| == 0 then ""
    else s[index..] + s[..index]
}

predicate isAllDigits(s: string)
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function parseInput(input: string): seq<string>
    ensures |parseInput(input)| >= 0
    decreases |input|
{
    parseInputHelper(input, 0, "", [])
}

function parseInputHelper(input: string, i: int, currentLine: string, lines: seq<string>): seq<string>
    requires 0 <= i <= |input|
    ensures |parseInputHelper(input, i, currentLine, lines)| >= |lines|
    decreases |input| - i
{
    if i >= |input| then
        if |currentLine| > 0 then lines + [currentLine] else lines
    else if input[i] == '\n' then
        parseInputHelper(input, i + 1, "", lines + [currentLine])
    else
        parseInputHelper(input, i + 1, currentLine + [input[i]], lines)
}

function parseInt(s: string): int
    ensures parseInt(s) >= 0
{
    if |s| == 0 then 0
    else if !('0' <= s[0] <= '9') then 0
    else (s[0] as int - '0' as int) + 10 * parseInt(s[1..])
}

// <vc-helpers>
lemma StringLessLeTrans(a: string, b: string, c: string)
    requires a < b && b <= c
    ensures a < c
{
    if b < c {
        calc {
            a;
            < b;
            < c;
        }
    } else {
        // b == c
        assert a < c;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
    ensures |result| > 0
    ensures result[|result| - 1] == '\n'
    ensures var lines := parseInput(stdin_input);
            if |lines| >= 2 then
                var n := parseInt(lines[0]);
                var digits := lines[1];
                if ValidInput(n, digits) then
                    var minResult := result[..|result|-1];
                    |minResult| == n &&
                    (forall i :: 0 <= i < |minResult| ==> '0' <= minResult[i] <= '9') &&
                    (exists index :: 0 <= index < n && minResult == modifyString(digits, index)) &&
                    (forall index :: 0 <= index < n ==> minResult <= modifyString(digits, index))
                else
                    result == "\n"
            else
                result == "\n"
// </vc-spec>
// <vc-code>
{
  var lines := parseInput(stdin_input);
  if |lines| < 2 {
    result := "\n";
    return;
  }

  var n := parseInt(lines[0]);
  var digits := lines[1];

  if !ValidInput(n, digits) {
    result := "\n";
    return;
  }

  // n > 0 and |digits| == n by ValidInput
  var i := 1;
  var min := modifyString(digits, 0);
  // loop to find minimal modification among indices 0..n-1
  while i < n
    invariant 0 <= i <= n
    invariant exists j :: 0 <= j < i && min == modifyString(digits, j)
    invariant forall k :: 0 <= k < i ==> min <= modifyString(digits, k)
    invariant |min| == n
    invariant isAllDigits(min)
    decreases n - i
  {
    var cur := modifyString(digits, i);
    if cur < min {
      // Prove that cur is <= all modifyString(digits, k) for k < i
      var kk := 0;
      while kk < i
        invariant 0 <= kk <= i
        invariant forall t :: 0 <= t < kk ==> cur < modifyString(digits, t)
      {
        // from outer loop invariant: min <= modifyString(digits, kk)
        assert min <= modifyString(digits, kk);
        StringLessLeTrans(cur, min, modifyString(digits, kk));
        // now cur < modifyString(digits, kk) holds for this kk
        kk := kk + 1;
      }
      min := cur;
      // after this assignment, forall k < i :: min <= modifyString(digits,k) holds
    }
    i := i + 1;
  }

  result := min + "\n";
}
// </vc-code>

