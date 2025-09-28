// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SliceLength<T>(s: seq<T>, a: int, b: int)
  requires 0 <= a <= b <= |s|
  ensures |s[a..b]| == b - a
{
  assert |s[a..b]| == b - a;
}

lemma ConcatSlices<T>(s: seq<T>, a: int, m: int, b: int)
  requires 0 <= a <= m <= b <= |s|
  ensures s[a..m] + s[m..b] == s[a..b]
{
  assert s[a..m] + s[m..b] == s[a..b];
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
  var left := oline[0..atPos];
  var middle := nl[0..p];
  var right := oline[atPos..l];
  result := left + middle + right;
}
// </vc-code>
