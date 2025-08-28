// method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
// //   ensures count == |set i | i in numbers && i < threshold|
//     ensures count == |SetLessThan(numbers, threshold)|
// {
//   count := 0;
//   var ss := numbers;
//   while ss != {}
//     decreases |ss|
//   {
//     var i: int :| i in ss;
//     ss := ss - {i};
//     if i < threshold {
//       count := count + 1;
//     }

//   }
//   assert count == |SetLessThan(numbers, threshold)|;
// //   assert count == |set i | i in numbers && i < threshold|;
// }

function SetLessThan(numbers: set<int>, threshold: int): set<int>
{
  set i | i in numbers && i < threshold
}


/*
*/

function seqSet(nums: seq<int>, index: nat): set<int> {
    set x | 0 <= x < index < |nums| :: nums[x]
}


// lemma numElemsOfSet(a: seq<int>)
//   requires sorted(a)
// {
//   assert distinct(a);
//   var s := set x | x in a;
//   assert forall x :: x in s ==> x in a[..];
//   assert forall x :: x in a ==> x in s;
//   assert |s| == |a|;
// }

// lemma CardinalitySetEqualsArray(a: seq<int>, s: set<int>)
//   requires s == set x | x in a
//   requires distinct(a)
//   ensures |s| == |a|
// {
//     assert forall x :: x in s ==> exists i :: 0 <= i < |a| && a[i] == x;
//     assert forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j];
//     // Assert that each element in the array is in the set
//     assert forall i :: 0 <= i < |a| ==> a[i] in s;
//     // Assert that the set contains exactly the elements in the array
//     assert s == set x | x in a;
//     // Assert that the set is a subset of the array
//     assert forall x :: x in s <==> x in a;

//     // Conclude the equivalence
//     assert |s| == |a|;
// }


/*


*/

// TODO play with this for keys==Contents


ghost predicate SortedSeq(a: seq<int>)
  //sequence is sorted from left to right
{
  (forall i,j :: 0<= i< j < |a| ==> ( a[i] < a[j] ))
}

method GetInsertIndex(a: array<int>, limit: int, x:int) returns (idx:int)
  // get index so that array stays sorted
  requires x !in a[..]
  requires 0 <= limit <= a.Length
  requires SortedSeq(a[..limit])
  ensures 0<= idx <= limit
  ensures SortedSeq(a[..limit])
  ensures idx > 0 ==> a[idx-1]< x
  ensures idx < limit ==> x < a[idx]
{
  assume{:axiom} false;
}

predicate sorted(a: seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

predicate distinct(a: seq<int>)
{
  forall i,j :: (0 <= i < |a| && 0 <= j < |a| && i != j) ==> a[i] != a[j]
}

predicate sorted_eq(a: seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate lessThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] < key
}

predicate greaterThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] > key
}

predicate greaterEqualThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] >= key
}
/*
method InsertSorted(a: array<int>, key: int ) returns (b: array<int>)
  requires sorted_eq(a[..])
  ensures sorted_eq(b[..])
{
  assume{:axiom} false;
}
*/

function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
    (if a[0] then 1 else 0) + count(a[1..])
}

// verifies in more than 45 seconds, but less than 100 seconds

// <vc-helpers>
lemma InsertPreservesSortedPrefix(a: seq<int>, limit: int, key: int, idx: int)
  requires 0 <= limit <= |a|
  requires sorted(a[..limit])
  requires key !in a[..limit]
  requires 0 <= idx <= limit
  requires idx > 0 ==> a[idx-1] < key
  requires idx < limit ==> key < a[idx]
  ensures sorted((a[..idx] + [key] + a[idx..limit])[..limit+1])
{
  var newSeq := a[..idx] + [key] + a[idx..limit];
  assert |newSeq| == limit + 1;
  assert forall i :: 0 <= i < idx ==> newSeq[i] == a[i];
  assert newSeq[idx] == key;
  assert forall i :: idx < i < limit + 1 ==> newSeq[i] == a[i-1];
  
  forall i, j | 0 <= i < j < limit + 1
    ensures newSeq[i] < newSeq[j]
  {
    if j == idx {
      if i < idx {
        assert newSeq[i] == a[i];
        assert newSeq[j] == key;
        if idx > 0 {
          assert a[idx-1] < key;
          assert i <= idx-1;
          assert a[i] <= a[idx-1] < key;
        }
      }
    } else if i == idx {
      assert newSeq[i] == key;
      assert newSeq[j] == a[j-1];
      assert idx < limit ==> key < a[idx];
      assert j > idx ==> j-1 >= idx;
      assert idx < limit ==> key < a[j-1];
    } else if i < idx < j {
      assert newSeq[i] == a[i];
      assert newSeq[j] == a[j-1];
      assert i < j-1 < limit;
      assert a[i] < a[j-1];
    } else if i < j <= idx {
      assert newSeq[i] == a[i];
      assert newSeq[j] == a[j];
      assert i < j <= limit;
      assert a[i] < a[j];
    } else {
      assert idx < i < j;
      assert newSeq[i] == a[i-1];
      assert newSeq[j] == a[j-1];
      assert i-1 < j-1 < limit;
      assert a[i-1] < a[j-1];
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method InsertIntoSorted(a: array<int>, limit:int, key:int) returns (b: array<int>)
    requires key > 0
    requires key !in a[..]
    requires 0 <= limit < a.Length
    requires forall i :: 0 <= i < limit ==> a[i] > 0
    requires forall i :: limit <= i < a.Length ==> a[i] == 0
    requires sorted(a[..limit]) 
    ensures b.Length == a.Length
    ensures sorted(b[..(limit+ 1)])
    ensures forall i :: limit + 1 <= i < b.Length ==> b[i] == 0  
    ensures forall i :: 0 <= i < limit ==> a[i] in b[..]
    ensures forall i :: 0 <= i < limit + 1 ==> b[i] > 0
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  b := new int[a.Length];
  var i := 0;
  while i < limit
    invariant 0 <= i <= limit
    invariant forall j :: 0 <= j < i ==> b[j] == a[j]
  {
    b[i] := a[i];
    i := i + 1;
  }
  while i < a.Length
    invariant limit <= i <= a.Length
    invariant forall j :: limit <= j < i ==> b[j] == 0
  {
    b[i] := 0;
    i := i + 1;
  }
  var idx := GetInsertIndex(a, limit, key);
  i := limit;
  while i > idx
    invariant idx <= i <= limit + 1
    invariant forall j :: 0 <= j < idx ==> b[j] == a[j]
    invariant forall j :: idx <= j < i ==> b[j] == a[j-1]
    invariant forall j :: i <= j < b.Length ==> b[j] == 0
  {
    b[i] := a[i-1];
    i := i - 1;
  }
  b[idx] := key;
  assert sorted(b[..limit+1]) by {
    InsertPreservesSortedPrefix(a[..limit], limit, key, idx);
    assert b[..limit+1] == (a[..idx] + [key] + a[idx..limit]);
  }
  assert forall i :: 0 <= i < limit ==> a[i] in b[..limit+1] by {
    forall i | 0 <= i < limit
      ensures a[i] in b[..limit+1]
    {
      if i < idx {
        assert b[i] == a[i];
      } else {
        assert b[i+1] == a[i];
      }
    }
  }
  assert forall i :: limit + 1 <= i < b.Length ==> b[i] == 0;
  assert forall i :: 0 <= i < limit + 1 ==> b[i] > 0 by {
    forall i | 0 <= i < limit + 1
      ensures b[i] > 0
    {
      if i < idx {
        assert b[i] == a[i] > 0;
      } else if i == idx {
        assert b[i] == key > 0;
      } else {
        assert b[i] == a[i-1] > 0;
      }
    }
  }
}
// </vc-code>
