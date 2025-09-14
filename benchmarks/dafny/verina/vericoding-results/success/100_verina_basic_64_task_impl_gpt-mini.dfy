// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Take<T>(s: seq<T>, n: int): seq<T> requires 0 <= n <= |s| { s[..n] }
function Drop<T>(s: seq<T>, n: int): seq<T> requires 0 <= n <= |s| { s[n..] }
lemma TakeDropConcat<T>(s: seq<T>, n: int) requires 0 <= n <= |s| ensures s == Take(s,n) + Drop(s,n) { }
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
  var left := oline[..atPos];
  var mid := nl[..p];
  var right := oline[atPos..l];
  result := left + mid + right;
}
// </vc-code>
