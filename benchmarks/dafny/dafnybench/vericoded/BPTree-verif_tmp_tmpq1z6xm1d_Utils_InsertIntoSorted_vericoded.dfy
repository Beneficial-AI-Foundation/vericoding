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
lemma SortedSubsetStillSorted(a: seq<int>, i: int, j: int)
    requires sorted(a)
    requires 0 <= i <= j <= |a|
    ensures sorted(a[i..j])
{
    assert forall x, y :: i <= x < y < j ==> a[x] < a[y];
}

lemma InsertPreservesSorted(a: seq<int>, idx: int, key: int)
    requires sorted(a)
    requires 0 <= idx <= |a|
    requires idx > 0 ==> a[idx-1] < key
    requires idx < |a| ==> key < a[idx]
    requires key !in a
    ensures sorted(a[..idx] + [key] + a[idx..])
{
    var result := a[..idx] + [key] + a[idx..];
    assert |result| == |a| + 1;
    
    forall i, j | 0 <= i < j < |result|
        ensures result[i] < result[j]
    {
        if j < idx {
            assert result[i] == a[i] && result[j] == a[j];
        } else if i < idx && j == idx {
            assert result[i] == a[i] && result[j] == key;
            if idx > 0 { assert a[i] < key; }
        } else if i < idx && j > idx {
            assert result[i] == a[i] && result[j] == a[j-1];
            assert a[i] < a[j-1];
        } else if i == idx && j > idx {
            assert result[i] == key && result[j] == a[j-1];
            if idx < |a| { assert key < a[idx]; assert a[idx] <= a[j-1]; }
        } else {
            assert i > idx && j > idx;
            assert result[i] == a[i-1] && result[j] == a[j-1];
            assert a[i-1] < a[j-1];
        }
    }
}

lemma AllElementsPreserved(a: array<int>, b: array<int>, idx: int, key: int, limit: int)
    requires 0 <= idx <= limit < a.Length
    requires b.Length == a.Length
    requires limit + 1 <= b.Length
    requires b[..limit+1] == a[..idx] + [key] + a[idx..limit]
    ensures forall j :: 0 <= j < limit ==> a[j] in b[..limit+1]
    ensures forall j :: 0 <= j < limit ==> a[j] in b[..]
{
    forall j | 0 <= j < limit
        ensures a[j] in b[..limit+1]
        ensures a[j] in b[..]
    {
        if j < idx {
            assert b[j] == a[j];
            assert a[j] in b[..limit+1];
        } else {
            assert j >= idx;
            assert b[j+1] == a[j];
            assert a[j] in b[..limit+1];
        }
        assert a[j] in b[..limit+1];
        assert b[..limit+1] <= b[..];
        assert a[j] in b[..];
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
    
    // Copy elements before insertion point
    var i := 0;
    while i < idx
        invariant 0 <= i <= idx
        invariant idx <= limit
        invariant forall j :: 0 <= j < i ==> b[j] == a[j]
    {
        b[i] := a[i];
        i := i + 1;
    }
    
    // Insert the key
    b[idx] := key;
    
    // Shift elements after insertion point
    i := idx;
    while i < limit
        invariant idx <= i <= limit
        invariant forall j :: 0 <= j < idx ==> b[j] == a[j]
        invariant b[idx] == key
        invariant forall j :: idx < j <= i ==> b[j] == a[j-1]
    {
        b[i + 1] := a[i];
        i := i + 1;
    }
    
    // At this point we have all elements copied/shifted
    assert forall j :: 0 <= j < idx ==> b[j] == a[j];
    assert b[idx] == key;
    assert forall j :: idx < j <= limit ==> b[j] == a[j-1];
    
    // Fill remaining with zeros
    i := limit + 1;
    while i < b.Length
        invariant limit + 1 <= i <= b.Length
        invariant forall j :: 0 <= j < idx ==> b[j] == a[j]
        invariant b[idx] == key
        invariant forall j :: idx < j <= limit ==> b[j] == a[j-1]
        invariant forall j :: limit + 1 <= j < i ==> b[j] == 0
    {
        b[i] := 0;
        i := i + 1;
    }
    
    // Now we can assert the full picture
    assert b[..limit+1] == a[..idx] + [key] + a[idx..limit];
    
    // Prove sorted property
    InsertPreservesSorted(a[..limit], idx, key);
    assert sorted(b[..limit+1]);
    
    // Prove all elements from a are preserved in b
    AllElementsPreserved(a, b, idx, key, limit);
    assert forall j :: 0 <= j < limit ==> a[j] in b[..];
}
// </vc-code>

