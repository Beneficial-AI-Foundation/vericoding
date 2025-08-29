// <vc-helpers>
predicate InList(x: int, lst: seq<int>)
{
  x in lst
}

predicate IsCommon(x: int, l1: seq<int>, l2: seq<int>)
{
  InList(x, l1) && InList(x, l2)
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate HasNoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function method SetToSortedSeq(s: set<int>): seq<int>
{
  if s == {} then []
  else 
    var min := SetMin(s);
    [min] + SetToSortedSeq(s - {min})
}

function SetMin(s: set<int>): int
  requires s != {}
{
  var x :| x in s;
  if forall y :: y in s ==> x <= y then x
  else SetMin(s - {x})
}

lemma SetToSortedSeqProperties(s: set<int>)
  ensures var result := SetToSortedSeq(s);
          IsSorted(result) && HasNoDuplicates(result) &&
          (forall x :: x in result <==> x in s)
{
  if s == {} {
    // Base case
  } else {
    var min := SetMin(s);
    var rest := SetToSortedSeq(s - {min});
    SetToSortedSeqProperties(s - {min});
    // Inductive case properties follow
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def common(l1: List[Int], l2: List[Int]) -> List[Int]
Return sorted unique common elements for two lists.
*/
// </vc-description>

// <vc-spec>
method common(l1: seq<int>, l2: seq<int>) returns (result: seq<int>)
  ensures IsSorted(result)
  ensures HasNoDuplicates(result)
  ensures forall x :: x in result <==> IsCommon(x, l1, l2)
// </vc-spec>
// <vc-code>
{
  var commonSet: set<int> := {};
  
  for i := 0 to |l1|
    invariant commonSet == set x | x in l1[..i] && x in l2
  {
    if l1[i] in l2 {
      commonSet := commonSet + {l1[i]};
    }
  }
  
  result := SetToSortedSeq(commonSet);
  SetToSortedSeqProperties(commonSet);
}
// </vc-code>
