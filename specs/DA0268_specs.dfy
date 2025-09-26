// <vc-preamble>
predicate ValidInput(a: seq<int>, b: seq<int>)
{
  |a| == |b| && |a| >= 2 && forall i :: 0 <= i < |a| ==> 0 <= a[i] <= b[i]
}

function sumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sumSeq(s[1..])
}

function findTwoLargestSum(s: seq<int>): int
  requires |s| >= 2
  ensures exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && 
          findTwoLargestSum(s) == s[i] + s[j] &&
          (forall k :: 0 <= k < |s| && k != i ==> s[k] <= s[i] || s[k] <= s[j]) &&
          (forall k :: 0 <= k < |s| && k != j ==> s[k] <= s[i] || s[k] <= s[j])
{
  var max1 := findMax(s);
  var max2 := findMaxExcluding(s, max1);
  s[max1] + s[max2]
}

function findMax(s: seq<int>): int
  requires |s| >= 1
  ensures 0 <= findMax(s) < |s|
  ensures forall i :: 0 <= i < |s| ==> s[i] <= s[findMax(s)]
{
  if |s| == 1 then 0
  else
    var restMax := findMax(s[1..]);
    if s[0] >= s[restMax + 1] then 0 else restMax + 1
}

function findMaxExcluding(s: seq<int>, exclude: int): int
  requires |s| >= 2
  requires 0 <= exclude < |s|
  ensures 0 <= findMaxExcluding(s, exclude) < |s|
  ensures findMaxExcluding(s, exclude) != exclude
  ensures forall i :: 0 <= i < |s| && i != exclude ==> s[i] <= s[findMaxExcluding(s, exclude)]
{
  if exclude == 0 then
    1 + findMax(s[1..])
  else if exclude == |s| - 1 then
    findMax(s[..|s|-1])
  else
    var leftMax := if |s[..exclude]| > 0 then findMax(s[..exclude]) else -1;
    var rightMax := if |s[exclude+1..]| > 0 then exclude + 1 + findMax(s[exclude+1..]) else -1;
    if leftMax == -1 then rightMax
    else if rightMax == -1 then leftMax
    else if s[leftMax] >= s[rightMax] then leftMax else rightMax
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>) returns (result: string)
  requires ValidInput(a, b)
  ensures result == "YES" || result == "NO"
  ensures result == "YES" <==> findTwoLargestSum(b) >= sumSeq(a)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
