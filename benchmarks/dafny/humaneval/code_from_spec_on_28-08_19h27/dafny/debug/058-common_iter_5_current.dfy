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

function SetToSortedSeq(s: set<int>): seq<int>
  decreases |s|
{
  if s == {} then []
  else 
    var min := SetMin(s);
    [min] + SetToSortedSeq(s - {min})
}

function SetMin(s: set<int>): int
  requires s != {}
  decreases |s|
{
  var x := SetPick(s);
  if forall y :: y in s ==> x <= y then x
  else SetMin(s - {x})
}

function SetPick(s: set<int>): int
  requires s != {}
  ensures SetPick(s) in s
{
  var x :| x in s; x
}

lemma SetToSortedSeqProperties(s: set<int>)
  ensures var result := SetToSortedSeq(s);
          IsSorted(result) && HasNoDuplicates(result) &&
          (forall x :: x in result <==> x in s)
  decreases |s|
{
  if s == {} {
    // Base case
  } else {
    var min := SetMin(s);
    SetMinIsMinimal(s);
    var rest := SetToSortedSeq(s - {min});
    SetToSortedSeqProperties(s - {min});
    
    // Prove IsSorted property
    var result := SetToSortedSeq(s);
    assert result == [min] + rest;
    assert IsSorted(rest);
    assert forall y :: y in (s - {min}) ==> min <= y;
    // Prove that result is sorted
    assert forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j] by {
      forall i, j | 0 <= i < j < |result|
        ensures result[i] <= result[j]
      {
        if i == 0 && j >= 1 {
          assert result[i] == min;
          if j == 1 {
            assert result[j] == rest[0];
            assert rest[0] in (s - {min});
            assert min <= rest[0];
          } else {
            assert result[j] == rest[j-1];
            assert rest[j-1] in (s - {min});
            assert min <= rest[j-1];
          }
        } else if i >= 1 && j >= 1 {
          assert result[i] == rest[i-1];
          assert result[j] == rest[j-1];
          assert 0 <= i-1 < j-1 < |rest|;
          assert rest[i-1] <= rest[j-1];
        }
      }
    }
    assert IsSorted(result);
    
    // Prove HasNoDuplicates property
    assert min !in rest;
    assert HasNoDuplicates(rest);
    assert HasNoDuplicates(result);
    
    // Prove set equivalence
    assert forall x :: x in result <==> x in s;
  }
}

lemma SetMinIsMinimal(s: set<int>)
  requires s != {}
  ensures var min := SetMin(s);
          min in s && (forall y :: y in s ==> min <= y)
  decreases |s|
{
  var x := SetPick(s);
  if forall y :: y in s ==> x <= y {
    // x is the minimum
    assert SetMin(s) == x;
    assert x in s;
  } else {
    assert exists z :: z in s && x > z;
    var s' := s - {x};
    assert |s'| < |s|;
    assert s' != {} by {
      assert exists z :: z in s && x > z;
      var witness :| witness in s && x > witness;
      assert witness != x;
      assert witness in s';
    }
    SetMinIsMinimal(s');
    var min := SetMin(s');
    assert min in s';
    assert forall y :: y in s' ==> min <= y;
    assert min in s;
    assert forall y :: y in s ==> min <= y by {
      forall y | y in s
        ensures min <= y
      {
        if y == x {
          assert min in s' && min <= x by {
            assert exists z :: z in s && x > z;
            var witness :| witness in s && x > witness;
            assert witness in s';
            assert min <= witness;
            assert witness < x;
            assert min <= x;
          }
        } else {
          assert y in s';
          assert min <= y;
        }
      }
    }
    assert SetMin(s) == min;
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
  
  // Prove the postcondition about common elements
  assert forall x :: x in result <==> x in commonSet;
  assert forall x :: x in commonSet <==> (x in l1 && x in l2);
  assert forall x :: x in result <==> IsCommon(x, l1, l2);
}
// </vc-code>
