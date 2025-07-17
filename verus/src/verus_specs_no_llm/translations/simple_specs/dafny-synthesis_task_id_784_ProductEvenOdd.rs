// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}
spec fn IsFirstEven(evenIndex: int, lst: Seq<int>) -> bool {
    forall |i: int| 0 <= i < evenIndex ==> IsOdd(lst.index(i))
}
spec fn IsFirstOdd(oddIndex: int, lst: Seq<int>) -> bool {
    forall |i: int| 0 <= i < oddIndex ==> IsEven(lst.index(i))
}
spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}

spec fn spec_FirstEvenOddIndices(lst: Seq<int>) -> evenIndex: int, oddIndex : int)
  requires |lst| >= 2
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures 0 <= evenIndex < |lst|
  ensures 0 <= oddIndex < |lst|
  // This is the postcondition that ensures that it's the first, not just any
  ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
  ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
  evenIndex := 0;
  oddIndex := 0;
  assume 0 <= evenIndex < |lst|;
  assume 0 <= oddIndex < |lst|;
  assume IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst);
  assume IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst);
  return evenIndex, oddIndex;
}


//ATOM

predicate IsFirstOdd(oddIndex: int, lst: seq<int>)
  requires 0 <= oddIndex < |lst|
  requires IsOdd(lst[oddIndex])
{
  forall i :: 0 <= i < oddIndex ==> IsEven(lst[i])
}


//ATOM

predicate IsOdd(n: int)
{
  n % 2 != 0
}


// SPEC

method ProductEvenOdd(lst: seq<int>) returns (product : int
    requires
        lst.len() >= 2,
        exists |i: int| 0 <= i < lst.len() && IsEven(lst.index(i)),
        exists |i: int| 0 <= i < lst.len() && IsOdd(lst.index(i)),
        0 <= oddIndex < lst.len(),
        IsOdd(lst.index(oddIndex)),
        lst.len() >= 2,
        exists |i: int| 0 <= i < lst.len() && IsEven(lst.index(i)),
        exists |i: int| 0 <= i < lst.len() && IsOdd(lst.index(i))
    ensures
        0 <= evenIndex < lst.len(),
        0 <= oddIndex < lst.len()
  // This is the postcondition that,
        that it's the first, not just any,
        IsEven(lst.index(evenIndex)) && IsFirstEven(evenIndex, lst),
        IsOdd(lst.index(oddIndex)) && IsFirstOdd(oddIndex, lst),
        exists |i: int, j: int| 0 <= i < lst.len() && IsEven(lst.index(i)) && IsFirstEven(i, lst) && 
              0 <= j < lst.len() && IsOdd(lst.index(j)) && IsFirstOdd(j, lst) && product == lst.index(i) * lst.index(j)
;

proof fn lemma_FirstEvenOddIndices(lst: Seq<int>) -> (evenIndex: int, oddIndex: int)
  requires |lst| >= 2
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures 0 <= evenIndex < |lst|
  ensures 0 <= oddIndex < |lst|
  // This is the postcondition that ensures that it's the first, not just any
  ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
  ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
  evenIndex: = 0;
  oddIndex := 0;
  assume 0 <= evenIndex < |lst|;
  assume 0 <= oddIndex < |lst|;
  assume IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst);
  assume IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst);
  return evenIndex, oddIndex;
}


//ATOM

predicate IsFirstOdd(oddIndex: int, lst: Seq<int>)
    requires
        lst.len() >= 2,
        exists |i: int| 0 <= i < lst.len() && IsEven(lst.index(i)),
        exists |i: int| 0 <= i < lst.len() && IsOdd(lst.index(i)),
        0 <= oddIndex < lst.len(),
        IsOdd(lst.index(oddIndex)),
        lst.len() >= 2,
        exists |i: int| 0 <= i < lst.len() && IsEven(lst.index(i)),
        exists |i: int| 0 <= i < lst.len() && IsOdd(lst.index(i))
    ensures
        0 <= evenIndex < lst.len(),
        0 <= oddIndex < lst.len()
  // This is the postcondition that,
        that it's the first, not just any,
        IsEven(lst.index(evenIndex)) && IsFirstEven(evenIndex, lst),
        IsOdd(lst.index(oddIndex)) && IsFirstOdd(oddIndex, lst),
        exists |i: int, j: int| 0 <= i < lst.len() && IsEven(lst.index(i)) && IsFirstEven(i, lst) && 
              0 <= j < lst.len() && IsOdd(lst.index(j)) && IsFirstOdd(j, lst) && product == lst.index(i) * lst.index(j)
{
    (0, 0, 0, 0, 0, 0, 0, 0, Seq::empty())
}

}