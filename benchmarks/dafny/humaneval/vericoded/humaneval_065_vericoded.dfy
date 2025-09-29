// <vc-preamble>

function intToString(x: int): string
    requires x >= 0
    ensures |intToString(x)| >= 1
    ensures forall i :: 0 <= i < |intToString(x)| ==> '0' <= intToString(x)[i] <= '9'
{
    if x == 0 then "0"
    else intToStringHelper(x, "")
}

function intToStringHelper(x: int, acc: string): string
    requires x >= 0
    requires forall i :: 0 <= i < |acc| ==> '0' <= acc[i] <= '9'
    ensures forall i :: 0 <= i < |intToStringHelper(x, acc)| ==> '0' <= intToStringHelper(x, acc)[i] <= '9'
    ensures x > 0 ==> |intToStringHelper(x, acc)| > |acc|
{
    if x == 0 then acc
    else intToStringHelper(x / 10, [((x % 10) + '0' as int) as char] + acc)
}

function reverseString(s: string): string
    ensures |reverseString(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> reverseString(s)[i] == s[|s| - 1 - i]
{
    if |s| <= 1 then s
    else reverseString(s[1..]) + [s[0]]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method circular_shift(x: int, shift: int) returns (result: string)
    ensures |result| == |intToString(if x < 0 then -x else x)|
    ensures shift > |intToString(if x < 0 then -x else x)| ==> 
            result == reverseString(intToString(if x < 0 then -x else x))
    ensures shift <= |intToString(if x < 0 then -x else x)| && |intToString(if x < 0 then -x else x)| > 0 ==>
            (var digits := intToString(if x < 0 then -x else x);
             var n := |digits|;
             var normalizedShift := shift % n;
             normalizedShift == 0 ==> result == digits)
    ensures shift <= |intToString(if x < 0 then -x else x)| && |intToString(if x < 0 then -x else x)| > 0 ==>
            (var digits := intToString(if x < 0 then -x else x);
             var n := |digits|;
             var normalizedShift := shift % n;
             normalizedShift > 0 ==> result == digits[n - normalizedShift..] + digits[..n - normalizedShift])
    ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
// </vc-spec>
// <vc-code>
{
  var absX := if x < 0 then -x else x;
  var digits := intToString(absX);
  var n := |digits|;
  
  if shift > n {
    result := reverseString(digits);
  } else if n == 0 {
    result := digits;
  } else {
    var normalizedShift := shift % n;
    if normalizedShift == 0 {
      result := digits;
    } else {
      result := digits[n - normalizedShift..] + digits[..n - normalizedShift];
    }
  }
}
// </vc-code>
