// <vc-preamble>
// A LIFO queue (aka a stack) with limited capacity.
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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Peek() returns (elem : int) 
      requires Valid() && !Empty()
      ensures elem == arr[top]
// </vc-spec>
// <vc-code>
{
            return arr[top]; 
}
// </vc-code>

// Pushed an element to the top of a (non full) stack. 

      // Pops the top element off the stack.





      //Push onto full stack, oldest element is discarded.




// When you are finished,  all the below assertions should be provable. 
// Feel free to add extra ones as well.

}