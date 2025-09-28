// <vc-preamble>
function max(a: int, b: int): int
{
    if a >= b then a else b
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

function MaxRcur(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| <= 1 then
        s[0]
    else
        max(s[|s|-1], MaxRcur(s[..|s|-1]))
}

function MinRcur(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| <= 1 then
        s[0]
    else
        min(s[|s|-1], MinRcur(s[..|s|-1]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed lemma assertions to match actual recursive definitions */
lemma MaxRcurLoop(s: seq<int>, i: int, currentMax: int)
  requires 0 < i <= |s|
  requires currentMax == MaxRcur(s[..i])
  requires i < |s|
  ensures max(currentMax, s[i]) == MaxRcur(s[..i+1])
{
  assert s[..i+1][|s[..i+1]|-1] == s[i];
  assert s[..i+1][..|s[..i+1]|-1] == s[..i];
  assert MaxRcur(s[..i+1]) == max(s[i], MaxRcur(s[..i]));
}

lemma MinRcurLoop(s: seq<int>, i: int, currentMin: int)
  requires 0 < i <= |s|
  requires currentMin == MinRcur(s[..i])
  requires i < |s|
  ensures min(currentMin, s[i]) == MinRcur(s[..i+1])
{
  assert s[..i+1][|s[..i+1]|-1] == s[i];
  assert s[..i+1][..|s[..i+1]|-1] == s[..i];
  assert MinRcur(s[..i+1]) == min(s[i], MinRcur(s[..i]));
}
// </vc-helpers>

// <vc-spec>
method SumMinMax(arr: array<int>) returns (sum: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures sum == MaxRcur(arr[..]) + MinRcur(arr[..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed final assertion with proper invariant maintenance */
  var maxVal := arr[0];
  var minVal := arr[0];
  var i := 1;
  
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant maxVal == MaxRcur(arr[..i])
    invariant minVal == MinRcur(arr[..i])
  {
    MaxRcurLoop(arr[..], i, maxVal);
    MinRcurLoop(arr[..], i, minVal);
    
    maxVal := max(maxVal, arr[i]);
    minVal := min(minVal, arr[i]);
    i := i + 1;
  }
  
  assert i == arr.Length;
  assert arr[..i] == arr[..];
  sum := maxVal + minVal;
}
// </vc-code>
