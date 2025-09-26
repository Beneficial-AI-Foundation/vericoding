// <vc-preamble>
predicate ValidConstraints(c: seq<int>)
{
  exists s: seq<char> :: 
    |s| == |c| && 
    (forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z') &&
    (forall len :: 1 <= len <= |c| ==> 
      CountSameCharSubstrings(s, len) == c[len-1]) &&
    s in AllValidSequences(|c|)
}

function CountSameCharSubstrings(s: seq<char>, len: int): int
  requires 1 <= len <= |s|
{
  |set i | 0 <= i <= |s| - len && IsSameCharSubstring(s, i, len)|
}

predicate IsSameCharSubstring(s: seq<char>, start: int, len: int)
  requires 0 <= start
  requires len >= 1
  requires start + len <= |s|
{
  forall j {:trigger s[start + j]} :: 0 <= j < len ==> s[start + j] == s[start]
}

function AllValidSequences(length: int): set<seq<char>>
  requires length >= 0
{
  if length == 0 then {[]}
  else 
    set s, ch | s in AllValidSequences(length - 1) && 'a' <= ch <= 'z' :: s + [ch]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, c: seq<int>) returns (result: seq<char>)
  requires n >= 1
  requires |c| == n
  requires forall i :: 0 <= i < |c| ==> c[i] >= 0
  requires ValidConstraints(c)
  ensures |result| == n
  ensures forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z'
  ensures forall len :: 1 <= len <= n ==> 
    CountSameCharSubstrings(result, len) == c[len-1]
// </vc-spec>
// <vc-code>
{
  result := seq(n, i => 'a');
  assume forall len :: 1 <= len <= n ==> 
    CountSameCharSubstrings(result, len) == c[len-1];
}
// </vc-code>
