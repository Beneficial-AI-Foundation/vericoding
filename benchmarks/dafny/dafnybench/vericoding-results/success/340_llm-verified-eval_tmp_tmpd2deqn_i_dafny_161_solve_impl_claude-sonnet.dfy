function IsLetter(c: char): bool 
{
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') 
}

function NoLetters(s: string, n: nat): bool 
  requires n <= |s|
{
  forall c :: 0 <= c < n ==> !IsLetter(s[c])
}

function ToggleCase(c: char): char
{
  if c >= 'a' && c <= 'z' 
  then 
    (c - 'a' + 'A')
  else if c >= 'A' && c <= 'Z' 
    then 
      (c - 'A' + 'a')
    else 
      c
}
function isReverse(s: string, s_prime: string): bool{
  (|s| == |s_prime|) &&
  (forall si :: 0 <= si < |s|/2 ==> s_prime[|s| - si - 1] == s[si])
}

method Reverse(original: seq<char>) returns (reversed: seq<char>)
  ensures |reversed| == |original| 
  ensures forall i :: 0 <= i < |original| ==> reversed[i] == original[|original| - 1 - i]
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma NoLettersEquivalent(s: string)
  ensures NoLetters(s, |s|) <==> forall i :: 0 <= i < |s| ==> !IsLetter(s[i])
{
}

lemma ToggleCasePreservesLength(s: string)
  ensures |s| == |seq(|s|, i requires 0 <= i < |s| => ToggleCase(s[i]))|
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  ensures |result| == |s| 
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && IsLetter(s[i]) ==> result[i] == ToggleCase(s[i])
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && !IsLetter(s[i]) ==> result[i] == s[i] 
  ensures NoLetters(s, |s|) ==> isReverse(result, s)
// </vc-spec>
// <vc-code>
{
  if NoLetters(s, |s|) {
    var s_seq := seq(|s|, i requires 0 <= i < |s| => s[i]);
    var reversed_seq := Reverse(s_seq);
    result := reversed_seq;
  } else {
    result := seq(|s|, i requires 0 <= i < |s| => if IsLetter(s[i]) then ToggleCase(s[i]) else s[i]);
  }
}
// </vc-code>

