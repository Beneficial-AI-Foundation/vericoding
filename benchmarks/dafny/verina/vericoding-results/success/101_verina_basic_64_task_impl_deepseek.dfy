// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function takeWhile(s: seq<char>, len: int): (r: seq<char>)
  requires 0 <= len <= |s|
  ensures |r| == len
  ensures r == s[0..len]
{
  if len == 0 then []
  else [s[0]] + takeWhile(s[1..], len - 1)
}

function dropWhile(s: seq<char>, from: int): (r: seq<char>)
  requires 0 <= from <= |s|
  ensures |r| == |s| - from
  ensures r == s[from..]
{
  if from == 0 then s
  else dropWhile(s[1..], from - 1)
}
// </vc-helpers>

// <vc-spec>
method Insert(oline: seq<char>, l: int, nl: seq<char>, p: int, atPos: int) returns (result: seq<char>)
    requires l <= |oline|
    requires p <= |nl|
    requires atPos <= l
    requires l >= 0
    requires p >= 0
    requires atPos >= 0
    ensures |result| == l + p
    ensures forall i :: 0 <= i < p ==> result[atPos + i] == nl[i]
    ensures forall i :: 0 <= i < atPos ==> result[i] == oline[i]
    ensures forall i {:trigger result[atPos + p + i]} :: 0 <= i < (l - atPos) ==> result[atPos + p + i] == oline[atPos + i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed length calculation to satisfy postcondition */
  var prefix := oline[0..atPos];
  var suffix := oline[atPos..l];
  result := prefix + nl[0..p] + suffix;
}
// </vc-code>
