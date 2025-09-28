// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>) 

    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed duplicate variable 'res' by removing redundant declaration */
  var n := |s|;
  var limit := n - n % 3;
  res := [];
  var i := 0;

  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> 
       (j < limit && j % 3 == 0 ==> res[j] == s[j + 1]) &&
       (j < limit && j % 3 == 1 ==> res[j] == s[j + 1]) &&
       (j < limit && j % 3 == 2 ==> res[j] == s[j - 2]) &&
       (j >= limit ==> res[j] == s[j])
  {
    if i < limit {
       if i % 3 == 0 || i % 3 == 1 {
          res := res + [s[i+1]];
       } else {
          res := res + [s[i-2]];
       }
    } else {
       res := res + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
