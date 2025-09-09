/*
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

/*
*/

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

//sequence is sorted from left to right

// get index so that array stays sorted

/*
method InsertSorted(a: array<int>, key: int ) returns (b: array<int>)
  requires sorted_eq(a[..])
  ensures sorted_eq(b[..])
{
  assume{:axiom} false;
}
*/

// verifies in more than 45 seconds, but less than 100 seconds
*/

function SetLessThan(numbers: set<int>, threshold: int): set<int>
{
  set i | i in numbers && i < threshold
}

function seqSet(nums: seq<int>, index: nat): set<int> {
    set x | 0 <= x < index < |nums| :: nums[x]
}

ghost predicate SortedSeq(a: seq<int>)

{
  (forall i,j :: 0<= i< j < |a| ==> ( a[i] < a[j] ))
}

method GetInsertIndex(a: array<int>, limit: int, x:int) returns (idx:int)

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
function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
    (if a[0] then 1 else 0) + count(a[1..])
}

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
