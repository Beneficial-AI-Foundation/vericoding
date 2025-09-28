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
/* helper modified by LLM (iteration 2): Added lemmas to prove loop invariants */
lemma MaxRcurExtend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MaxRcur(s + [x]) == max(x, MaxRcur(s))
{
  if |s| == 1 {
    assert s + [x] == [s[0], x];
    assert MaxRcur(s + [x]) == max(x, s[0]);
    assert MaxRcur(s) == s[0];
  } else {
    assert (s + [x])[..|s + [x]| - 1] == s;
  }
}

lemma MinRcurExtend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MinRcur(s + [x]) == min(x, MinRcur(s))
{
  if |s| == 1 {
    assert s + [x] == [s[0], x];
    assert MinRcur(s + [x]) == min(x, s[0]);
    assert MinRcur(s) == s[0];
  } else {
    assert (s + [x])[..|s + [x]| - 1] == s;
  }
}
// </vc-helpers>

// <vc-spec>
method SumMinMax(arr: array<int>) returns (sum: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures sum == MaxRcur(arr[..]) + MinRcur(arr[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariants using helper lemmas */
{
  var maxVal := arr[0];
  var minVal := arr[0];
  var i := 1;
  
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant maxVal == MaxRcur(arr[..i])
    invariant minVal == MinRcur(arr[..i])
  {
    assert arr[..i+1] == arr[..i] + [arr[i]];
    MaxRcurExtend(arr[..i], arr[i]);
    MinRcurExtend(arr[..i], arr[i]);
    
    maxVal := max(arr[i], maxVal);
    minVal := min(arr[i], minVal);
    i := i + 1;
  }
  
  assert arr[..i] == arr[..];
  sum := maxVal + minVal;
}
// </vc-code>
