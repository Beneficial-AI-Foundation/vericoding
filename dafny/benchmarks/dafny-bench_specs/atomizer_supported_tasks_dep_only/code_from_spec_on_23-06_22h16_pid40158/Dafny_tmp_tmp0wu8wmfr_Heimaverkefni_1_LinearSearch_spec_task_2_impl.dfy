// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/0HRr

// Author of solution:    Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/8pxWd

// Use the command
//   dafny LinearSearch-skeleton.dfy
// or
//   compile LinearSearch-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.



//ATOM_PLACEHOLDER_SearchRecursive





//IMPL SearchLoop
method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
{
    /* code modified by LLM (iteration 1): Changed approach to find the last occurrence of x instead of first */
    var index := j - 1;
    while index >= i
        invariant i - 1 <= index <= j - 1
        invariant forall r | index < r < j :: a[r] != x
    {
        if a[index] == x {
            return index;
        }
        index := index - 1;
    }
    return -1;
}