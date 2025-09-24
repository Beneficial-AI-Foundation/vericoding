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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Init(c : int)
      modifies this;
      requires c > 0
      ensures Valid() && Empty() && c == capacity
      ensures fresh(arr); // ensures arr is a newly created object.
      // Additional post-condition to be given here!
// </vc-spec>
// <vc-code>
{
        capacity := c;
        arr := new int[c];
        top := -1;
}
// </vc-code>

// Returns the top element of the stack, without removing it.



      // Pushed an element to the top of a (non full) stack. 

      // Pops the top element off the stack.





      //Push onto full stack, oldest element is discarded.




// When you are finished,  all the below assertions should be provable. 
// Feel free to add extra ones as well.

}