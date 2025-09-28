// <vc-preamble>
// Helper predicate to check if a sequence is sorted in ascending order
ghost predicate IsSorted(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if a sequence has no duplicate elements
ghost predicate IsUnique(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// Helper predicate to check if all elements from source appear in target
ghost predicate AllElementsIn(source: seq<real>, target: seq<real>)
{
    forall x :: x in source ==> x in target
}

// Helper predicate to check if all elements in target come from one of the sources
ghost predicate AllElementsFrom(target: seq<real>, source1: seq<real>, source2: seq<real>)
{
    forall x :: x in target ==> x in source1 || x in source2
}

// Method to compute the union of two sequences, returning sorted unique elements
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed syntax error by removing while loop from function */
function InsertSorted(s: seq<real>, x: real): seq<real>
  requires IsSorted(s)
  requires IsUnique(s)
  requires x !in s
  ensures IsSorted(InsertSorted(s, x))
  ensures IsUnique(InsertSorted(s, x))
  ensures |InsertSorted(s, x)| == |s| + 1
  ensures forall y :: y in s ==> y in InsertSorted(s, x)
  ensures x in InsertSorted(s, x)
  ensures forall y :: y in InsertSorted(s, x) ==> y in s || y == x
{
  if |s| == 0 then [x]
  else if x < s[0] then [x] + s
  else if x > s[|s|-1] then s + [x]
  else
    InsertHelper(s, x, 0)
}

function InsertHelper(s: seq<real>, x: real, i: int): seq<real>
  requires 0 <= i <= |s|
  requires IsSorted(s)
  requires IsUnique(s)
  requires x !in s
  requires i == |s| || s[i] > x
  requires forall j :: 0 <= j < i ==> s[j] < x
  decreases |s| - i
{
  if i == |s| then s + [x]
  else if s[i] > x then s[..i] + [x] + s[i..]
  else InsertHelper(s, x, i + 1)
}

function AddToUnion(current: seq<real>, elem: real): seq<real>
  requires IsSorted(current)
  requires IsUnique(current)
  ensures IsSorted(AddToUnion(current, elem))
  ensures IsUnique(AddToUnion(current, elem))
  ensures elem in AddToUnion(current, elem)
  ensures forall x :: x in current ==> x in AddToUnion(current, elem)
  ensures forall x :: x in AddToUnion(current, elem) ==> x in current || x == elem
  ensures |AddToUnion(current, elem)| <= |current| + 1
{
  if elem in current then current
  else InsertSorted(current, elem)
}

function UnionHelper(current: seq<real>, remaining: seq<real>): seq<real>
  requires IsSorted(current)
  requires IsUnique(current)
  ensures IsSorted(UnionHelper(current, remaining))
  ensures IsUnique(UnionHelper(current, remaining))
  ensures forall x :: x in current ==> x in UnionHelper(current, remaining)
  ensures forall x :: x in remaining ==> x in UnionHelper(current, remaining)
  ensures forall x :: x in UnionHelper(current, remaining) ==> x in current || x in remaining
  ensures |UnionHelper(current, remaining)| <= |current| + |remaining|
  decreases |remaining|
{
  if |remaining| == 0 then current
  else UnionHelper(AddToUnion(current, remaining[0]), remaining[1..])
}
// </vc-helpers>

// <vc-spec>
method Union1d(ar1: seq<real>, ar2: seq<real>) returns (result: seq<real>)
    ensures IsSorted(result)
    ensures IsUnique(result)
    ensures AllElementsIn(ar1, result)
    ensures AllElementsIn(ar2, result)
    ensures AllElementsFrom(result, ar1, ar2)
    ensures |result| <= |ar1| + |ar2|
    ensures forall s :: (IsSorted(s) && IsUnique(s) && 
                        AllElementsIn(ar1, s) && AllElementsIn(ar2, s) && 
                        AllElementsFrom(s, ar1, ar2)) ==> |result| <= |s|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): No change needed, using helper functions */
{
  var unionSeq := UnionHelper([], ar1);
  result := UnionHelper(unionSeq, ar2);
}
// </vc-code>
