class LimitedStack{

      var capacity : int; // capacity, max number of elements allowed on the stack.
      var arr : array<int>; // contents of stack.
      var top : int; // The index of the top of the stack, or -1 if the stack is empty

      // This predicate express a class invariant: All objects of this calls should satisfy this.
      predicate Valid()
      reads this;
      {
        arr != null && capacity > 0 && capacity == arr.Length &&  top >= -1 && top < capacity 
      }

      predicate Empty()
      reads this`top;
      {
            top == -1
      }

      predicate Full()
      reads this`top, this`capacity;
      {
        top == (capacity - 1)
      }







      // Returns the top element of the stack, without removing it.



      // Pushed an element to the top of a (non full) stack. 

      // Pops the top element off the stack.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Shift()
      requires Valid() && !Empty();
      ensures Valid();
      ensures forall i : int :: 0 <= i < capacity - 1 ==> arr[i] == old(arr[i + 1]);
      ensures top == old(top) - 1;
      modifies this.arr, this`top;
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var oldTop := top;
  
  while i < top
    invariant 0 <= i <= top
    invariant top == oldTop
    invariant arr != null
    invariant arr.Length == capacity
    invariant capacity > 0
    invariant top >= 0
    invariant top < capacity
    invariant forall j : int :: 0 <= j < i ==> arr[j] == old(arr[j + 1])
    invariant forall j : int :: i < j <= top ==> arr[j] == old(arr[j])
  {
    arr[i] := arr[i + 1];
    i := i + 1;
  }
  top := top - 1;
}
// </vc-code>

//Push onto full stack, oldest element is discarded.




// When you are finished,  all the below assertions should be provable. 
// Feel free to add extra ones as well.

}