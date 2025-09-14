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
lemma InsertPreservesElements(a: seq<int>, key: int, idx: int)
    requires 0 <= idx <= |a|
    requires key !in a
    ensures forall x :: x in a ==> x in a[..idx] + [key] + a[idx..]
    ensures forall x :: x in a[..idx] + [key] + a[idx..] && x != key ==> x in a
{
}

lemma InsertMaintainsSorted(a: seq<int>, key: int, idx: int)
    requires sorted(a)
    requires 0 <= idx <= |a|
    requires idx > 0 ==> a[idx-1] < key
    requires idx < |a| ==> key < a[idx]
    ensures sorted(a[..idx] + [key] + a[idx..])
{
    var result := a[..idx] + [key] + a[idx..];
    forall i, j | 0 <= i < j < |result|
        ensures result[i] < result[j]
    {
        if i < idx && j < idx {
            assert result[i] == a[i] && result[j] == a[j];
        } else if i < idx && j == idx {
            assert result[i] == a[i] && result[j] == key;
        } else if i < idx && j > idx {
            assert result[i] == a[i] && result[j] == a[j-1];
        } else if i == idx && j > idx {
            assert result[i] == key && result[j] == a[j-1];
        } else if i > idx && j > idx {
            assert result[i] == a[i-1] && result[j] == a[j-1];
        }
    }
}

lemma ElementsInResult(a: array<int>, b: array<int>, limit: int, idx: int)
    requires 0 <= idx <= limit < a.Length
    requires b.Length == a.Length
    requires forall k :: 0 <= k < idx && k < b.Length ==> b[k] == a[k]
    requires idx < b.Length ==> b[idx] > 0
    requires forall k :: idx + 1 <= k <= limit && k < b.Length ==> b[k] == a[k-1]
    ensures forall i :: 0 <= i < limit ==> a[i] in b[..]
{
    forall i | 0 <= i < limit
        ensures a[i] in b[..]
    {
        if i < idx {
            assert b[i] == a[i];
            assert a[i] in b[..];
        } else {
            assert i >= idx;
            assert i + 1 <= limit;
            assert b[i+1] == a[i];
            assert a[i] in b[..];
        }
    }
}
// </vc-helpers>

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
// <vc-code>
{
    var idx := GetInsertIndex(a, limit, key);
    b := new int[a.Length];
    
    var i := 0;
    while i < idx
        invariant 0 <= i <= idx
        invariant forall k :: 0 <= k < i ==> b[k] == a[k]
    {
        b[i] := a[i];
        i := i + 1;
    }
    
    b[idx] := key;
    
    i := idx + 1;
    while i <= limit
        invariant idx + 1 <= i <= limit + 1
        invariant forall k :: 0 <= k < idx ==> b[k] == a[k]
        invariant b[idx] == key
        invariant forall k :: idx + 1 <= k < i ==> b[k] == a[k-1]
    {
        b[i] := a[i-1];
        i := i + 1;
    }
    
    i := limit + 1;
    while i < a.Length
        invariant limit + 1 <= i <= a.Length
        invariant forall k :: 0 <= k < idx ==> b[k] == a[k]
        invariant b[idx] == key
        invariant forall k :: idx + 1 <= k <= limit ==> b[k] == a[k-1]
        invariant forall k :: limit + 1 <= k < i ==> b[k] == 0
    {
        b[i] := 0;
        i := i + 1;
    }
    
    assert b[..limit+1] == a[..idx] + [key] + a[idx..limit];
    InsertMaintainsSorted(a[..limit], key, idx);
    InsertPreservesElements(a[..limit], key, idx);
    ElementsInResult(a, b, limit, idx);
}
// </vc-code>

