use vstd::prelude::*;

verus! {

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

// function SetLessThan(numbers: set<int>, threshold: int): set<int>
// {
//   set i | i in numbers && i < threshold
// }

spec fn set_less_than(numbers: Set<int>, threshold: int) -> Set<int> {
    numbers.filter(|i: int| i < threshold)
}


/*
*/

// function seqSet(nums: seq<int>, index: nat): set<int> {
//     set x | 0 <= x < index < |nums| :: nums[x]
// }

spec fn seq_set(nums: Seq<int>, index: nat) -> Set<int> 
    recommends index <= nums.len()
{
    Set::new(|x: int| exists |i: int| 0 <= i < index && i < nums.len() && nums[i] == x)
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


// ghost predicate SortedSeq(a: seq<int>)
//   //sequence is sorted from left to right
// {
//   (forall i,j :: 0<= i< j < |a| ==> ( a[i] < a[j] ))
// }

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
}

// predicate sorted(a: seq<int>)
// {
//   forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
// }

spec fn sorted(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
}

// predicate distinct(a: seq<int>)
// {
//   forall i,j :: (0 <= i < |a| && 0 <= j < |a| && i != j) ==> a[i] != a[j]
// }

spec fn distinct(a: Seq<int>) -> bool {
    forall |i: int, j: int| (0 <= i < a.len() && 0 <= j < a.len() && i != j) ==> a[i] != a[j]
}

// predicate sorted_eq(a: seq<int>)
// {
//   forall i,j :: 0 <= i < j < |a| ==> a[i] <= a[j]
// }

spec fn sorted_eq(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// predicate lessThan(a:seq<int>, key:int) {
//   forall i :: 0 <= i < |a| ==> a[i] < key
// }

spec fn less_than(a: Seq<int>, key: int) -> bool {
    forall |i: int| 0 <= i < a.len() ==> a[i] < key
}

// predicate greaterThan(a:seq<int>, key:int) {
//   forall i :: 0 <= i < |a| ==> a[i] > key
// }

spec fn greater_than(a: Seq<int>, key: int) -> bool {
    forall |i: int| 0 <= i < a.len() ==> a[i] > key
}

// predicate greaterEqualThan(a:seq<int>, key:int) {
//   forall i :: 0 <= i < |a| ==> a[i] >= key
// }

spec fn greater_equal_than(a: Seq<int>, key: int) -> bool {
    forall |i: int| 0 <= i < a.len() ==> a[i] >= key
}
/*
method InsertSorted(a: array<int>, key: int ) returns (b: array<int>)
  requires sorted_eq(a[..])
  ensures sorted_eq(b[..])
{
  assume{:axiom} false;
}
*/

// function count(a: seq<bool>): nat
// {
//   if |a| == 0 then 0 else
//     (if a[0] then 1 else 0) + count(a[1..])
// }

spec fn count(a: Seq<bool>) -> nat 
    decreases a.len()
{
    if a.len() == 0 {
        0nat
    } else {
        (if a[0] { 1nat } else { 0nat }) + count(a.subrange(1, a.len() as int))
    }
}

// verifies in more than 45 seconds, but less than 100 seconds
// method InsertIntoSorted(a: array<int>, limit:int, key:int) returns (b: array<int>)
//     requires key > 0
//     requires key !in a[..]
//     requires 0 <= limit < a.Length
//     requires forall i :: 0 <= i < limit ==> a[i] > 0
//     requires forall i :: limit <= i < a.Length ==> a[i] == 0
//     requires sorted(a[..limit]) 
//     ensures b.Length == a.Length
//     ensures sorted(b[..(limit+ 1)])
//     ensures forall i :: limit + 1 <= i < b.Length ==> b[i] == 0  
//     ensures forall i :: 0 <= i < limit ==> a[i] in b[..]
//     ensures forall i :: 0 <= i < limit + 1 ==> b[i] > 0
// {
//   assume{:axiom} false;
// }

fn insert_into_sorted(a: Vec<int>, limit: usize, key: int) -> (b: Vec<int>)
    requires
        key > 0,
        !a@.contains(key),
        limit < a.len(),
        forall |i: int| 0 <= i < limit ==> a@[i] > 0,
        forall |i: int| limit <= i < a.len() ==> a@[i] == 0,
        sorted(a@.subrange(0, limit as int)),
    ensures
        b.len() == a.len(),
        sorted(b@.subrange(0, limit as int + 1)),
        forall |i: int| limit + 1 <= i < b.len() ==> b@[i] == 0,
        forall |i: int| 0 <= i < limit ==> a@.contains(b@[i]),
        forall |i: int| 0 <= i < limit + 1 ==> b@[i] > 0,
{
    assume(false);
    Vec::new()
}

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
// method GetInsertIndex(a: array<int>, limit: int, x:int) returns (idx:int)
//   // get index so that array stays sorted
//   requires x !in a[..]
//   requires 0 <= limit <= a.Length
//   requires SortedSeq(a[..limit])
//   ensures 0<= idx <= limit
//   ensures SortedSeq(a[..limit])
//   ensures idx > 0 ==> a[idx-1]< x
//   ensures idx < limit ==> x < a[idx]
fn get_insert_index(a: &Vec<int>, limit: usize, x: int) -> (idx: usize)
    // get index so that array stays sorted
    requires
        !a@.contains(x),
        limit <= a.len(),
        sorted_seq(a@.subrange(0, limit as int)),
    ensures
        idx <= limit,
        sorted_seq(a@.subrange(0, limit as int)),
        idx > 0 ==> a@[idx as int - 1] < x,
        idx < limit ==> x < a@[idx as int],
// </vc-spec>
// <vc-code>
{
    let mut idx: usize = 0;
    
    while idx < limit
        invariant
            0 <= idx <= limit,
            limit <= a.len(),
            sorted_seq(a@.subrange(0, limit as int)),
            forall |j: int| 0 <= j < idx ==> a@[j] < x,
            !a@.contains(x),
        decreases limit - idx,
    {
        assert(idx < limit);
        assert(limit <= a.len());
        assert(idx < a.len());
        
        if a[idx] > x {
            // Found the position where x should be inserted
            assert(idx > 0 ==> a@[idx as int - 1] < x);
            assert(x < a@[idx as int]);
            return idx;
        }
        
        // a[idx] <= x, but since x is not in the array and the array is sorted, a[idx] < x
        assert(a@[idx as int] <= x);
        assert(!a@.contains(x));
        assert(a@[idx as int] != x);
        assert(a@[idx as int] < x);
        
        idx = idx + 1;
    }
    
    // If we reach here, x is greater than all elements in a[..limit]
    assert(idx == limit);
    assert(forall |j: int| 0 <= j < limit ==> a@[j] < x);
    assert(idx > 0 ==> a@[idx as int - 1] < x);
    
    idx
}
// </vc-code>

fn main() {}

}