// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Valid() -> bool {
    0 <= counter <= circularQueue.len() &&
    0 <= front &&
    0 <= rear &&
    Content == circularQueue.spec_index(..)
}

fn insert(item: int)
     requires rear <= circularQueue.Length
     ensures (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
         (
           Content == [item] &&
           |Content| == 1
         )
  {}
    // ensures circularQueue.Length != 0 ==>
    // (
    //   (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == old(Content)  &&
    //       |Content| == old(|Content|)

    //     )
    // ||
    //   (front == 0 && rear == circularQueue.Length-1 ) ==> 
    //     (
    //       Content == old(Content) + [item] &&
    //       |Content| == old(|Content|) + 1
    //     )
    // ||
    //   (rear + 1 != front && rear != circularQueue.Length-1 && rear + 1 < circularQueue.Length - 1) ==> 
    //     (
    //       Content == old(Content[0..rear]) + [item] + old(Content[rear..circularQueue.Length])
    //     )
    // ||
    //   (rear + 1 == front) ==> 
    //   (
    //     Content[0..rear + 1] == old(Content[0..rear]) + [item] &&
    //     forall i :: rear + 2 <= i <= circularQueue.Length ==> Content[i] == old(Content[i-1])
    //   )
    // )
    // {

      //counter := counter + 1;
      // if front == 0 && rear == 0 && circularQueue.Length == 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [circularQueue.Length + 1];
      //   queueInsert[0] := item;
      //   circularQueue := queueInsert;
      //   Content := [item];
      //   rear := rear + 1;
      // }   
      // else if front == 0 && rear == circularQueue.Length-1 && circularQueue.Length > 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [circularQueue.Length + 1];
      //   var i: nat := 0;
      //   while i < circularQueue.Length
      //   invariant circularQueue.Length + 1 == queueInsert.Length
      //   {
      //     queueInsert[i] := circularQueue[i];
      //     i := i + 1;
      //   }
      //   queueInsert[queueInsert.Length - 1] := item;
      //   Content := Content + [item];
      //   rear := rear + 1;
      //   circularQueue := queueInsert;
      // }
    

  //SPEC
  method auxInsertEmptyQueue(item:int)
    requires front == 0 && rear == 0 && circularQueue.Length == 0
    ensures circularQueue.Length == 1
    ensures Content == [item]
    ensures |Content| == 1
    ensures rear == 1
    ensures counter == old(counter) + 1
    ensures front == 0
  {}

  //SPEC
  method auxInsertEndQueue(item:int)
    requires front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
  {}

  //SPEC
  method auxInsertSpaceQueue(item:int)
    requires rear < front && front < circularQueue.Length
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length])
    ensures |Content| == old(|Content|) + 1
  {}

  //SPEC
  method auxInsertInitQueue(item:int)
  {}

  //SPEC
  method auxInsertBetweenQueue(item:int)
  {}

  //SPEC
  method remove() -> (item: int)
    requires
        rear <= circularQueue.len(),
        front == 0 && rear == 0 && circularQueue.len() == 0,
        front == 0 && rear == circularQueue.len() && circularQueue.len() >= 1,
        rear < front && front < circularQueue.len(),
        front < circularQueue.len(),
        circularQueue.len() > 0
    ensures
        (front == 0 && rear == 0 && circularQueue.len() == 1) ==>
         (
           Content == [item] &&
           Content.len() == 1
         ),
        circularQueue.len() != 0 ==>
    // (
    //   (front == 0 && rear == 0 && circularQueue.len() == 1) ==>
    //     (
    //       Content == old(Content)  &&
    //       Content.len() == old(Content.len())

    //     )
    // |
    //   (front == 0 && rear == circularQueue.len()-1 ) ==> 
    //     (
    //       Content == old(Content) + [item] &&
    //       .len()Content == old(.len()Content) + 1
    //     )
    // .len()
    //   (rear + 1 != front && rear != circularQueue.len()-1 && rear + 1 < circularQueue.len() - 1) ==> 
    //     (
    //       Content == old(Content.spec_index(0..rear)) + [item] + old(Content.spec_index(rear..circularQueue.len()))
    //     )
    // .len()|
    //   (rear + 1 == front) ==> 
    //   (
    //     Content.spec_index(0..rear + 1) == old(Content.spec_index(0..rear)) + [item] &&
    //     forall i :: rear + 2 <= i <= circularQueue.len() ==> Content.spec_index(i) == old(Content.spec_index(i-1))
    //   )
    // )
    //,
        circularQueue.len() == 1,
        Content == [item],
        Content.len() == 1,
        rear == 1,
        counter == old(counter) + 1,
        front == 0,
        Content == old(Content) + [item],
        Content.len() == old(Content.len()) + 1,
        front == 0,
        rear == old(rear) + 1,
        counter == old(counter) + 1,
        rear == old(rear) + 1,
        counter == old(counter) + 1,
        Content == old(Content.spec_index(0..rear)) + [item] + old(Content.spec_index(rear+1..circularQueue.len())),
        Content.len() == old(Content.len()) + 1,
        rear <= old(Content).len(),
        circularQueue.len() > 0,
        item == old(Content)[old(front)],
        front == (old(front) + 1) % circularQueue.len(),
        old(front) < rear ==> Content == old(Content)[old(front)..rear],
        old(front) > rear ==> Content == old(Content)[0 .. rear] + old(Content)[old(front)..old(Content).len()]
{
    return 0;
}

}