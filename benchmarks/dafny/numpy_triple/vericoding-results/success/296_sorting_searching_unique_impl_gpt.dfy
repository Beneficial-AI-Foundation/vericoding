// <vc-preamble>
// Method to find unique elements in an array, removing duplicates and sorting
// </vc-preamble>

// <vc-helpers>
predicate StrictlyIncreasing(a: seq<real>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

/* helper modified by LLM (iteration 5): rewrite minIndex without let-in syntax to fix parsing */
function minIndex(s: seq<real>): nat
  requires |s| > 0
  ensures minIndex(s) < |s|
  ensures forall j :: 0 <= j < |s| ==> s[minIndex(s)] <= s[j]
  decreases |s|
{
  if |s| == 1 then 0
  else if s[0] <= s[minIndex(s[1..]) + 1] then 0 else minIndex(s[1..]) + 1
}

/* helper modified by LLM (iteration 5): minOfSeq defined via minIndex */
function minOfSeq(s: seq<real>): real
  requires |s| > 0
  ensures minOfSeq(s) in s
  ensures forall y :: y in s ==> minOfSeq(s) <= y
  decreases |s|
{
  s[minIndex(s)]
}

function removeAll(s: seq<real>, x: real): seq<real>
  ensures forall y :: y in removeAll(s, x) <==> y in s && y != x
  ensures (x in s) ==> |removeAll(s, x)| < |s|
  ensures (x !in s) ==> removeAll(s, x) == s
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] == x then removeAll(s[1..], x)
  else [s[0]] + removeAll(s[1..], x)
}

function uniqueSorted(s: seq<real>): seq<real>
  ensures |uniqueSorted(s)| <= |s|
  ensures forall x :: x in s <==> x in uniqueSorted(s)
  ensures forall i, j :: 0 <= i < j < |uniqueSorted(s)| ==> uniqueSorted(s)[i] < uniqueSorted(s)[j]
  decreases |s|
{
  if |s| == 0 then []
  else [minOfSeq(s)] + uniqueSorted(removeAll(s, minOfSeq(s)))
}
// </vc-helpers>

// <vc-spec>
method unique(ar: seq<real>) returns (result: seq<real>)
  // No preconditions - works on any input array
  ensures |result| <= |ar|
  // The result is sorted in ascending order
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
  // No duplicates in the result (defines uniqueness)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  // Every element in result comes from the input array
  ensures forall i :: 0 <= i < |result| ==> result[i] in ar
  // Every distinct element from input appears exactly once in result  
  ensures forall x :: x in ar ==> x in result
  ensures forall x :: x in result ==> x in ar
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): delegate to uniqueSorted helper ensuring sorted unique */
  result := uniqueSorted(ar);
}
// </vc-code>
