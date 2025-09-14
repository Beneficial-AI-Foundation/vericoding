// <vc-preamble>
datatype Option<T> = None | Some(value: T)

function CountFrequencyRcr(s: seq<char>, key: char): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountFrequencyRcr(s[..|s|-1], key) + if (s[|s|-1] == key) then
            1
        else
            0
}

predicate CheckFirstRepeatedChar(str1: seq<char>, repeated_char: Option<(nat, char)>)
{
    match repeated_char
    case None =>
        forall k :: 0 <= k < |str1| ==> CountFrequencyRcr(str1, str1[k]) <= 1
    case Some(pair) =>
        var idx := pair.0;
        var rp_char := pair.1;
        && idx as int <= |str1|
        && (forall i :: 0 <= i < idx as int ==> CountFrequencyRcr(str1, str1[i]) <= 1)
        && CountFrequencyRcr(str1, rp_char) > 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): CountFrequencyRcr is non-negative */
function CountNonNegative(s: seq<char>, key: char): bool { CountFrequencyRcr(s, key) >= 0 }
// </vc-helpers>

// <vc-spec>
method FirstRepeatedChar(str1: array<char>) returns (repeated_char: Option<(nat, char)>)
    ensures CheckFirstRepeatedChar(str1[..], repeated_char)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate over sequence to find first repeated character */
  var sseq := str1[..];
  var n := |sseq|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> CountFrequencyRcr(sseq, sseq[k]) <= 1
    decreases n - i
  {
    var c := sseq[i];
    if CountFrequencyRcr(sseq, c) > 1 {
      repeated_char := Some((i as nat, c));
      return;
    }
    i := i + 1;
  }
  repeated_char := None;
}
// </vc-code>
