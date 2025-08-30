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



//IMPL SearchRecursive
method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
    /* code modified by LLM (iteration 2): added decreases clause for termination */
    decreases j - i
{
    if i >= j {
        k := -1;
    } else {
        /* code modified by LLM (iteration 2): check rightmost element first, then recurse on remaining elements */
        if a[j-1] == x {
            k := j-1;
        } else {
            k := SearchRecursive(a, i, j-1, x);
        }
    }
}

//IMPL SearchLoop
method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
{
    k := -1;
    /* code modified by LLM (iteration 2): search backwards to find the rightmost occurrence */
    var idx := j - 1;
    while idx >= i
        invariant i - 1 <= idx < j
        invariant k == -1 || (i <= k < j && a[k] == x)
        invariant k != -1 ==> forall r | k < r < j :: a[r] != x
        invariant k == -1 ==> forall r | idx + 1 <= r < j :: a[r] != x
        /* code modified by LLM (iteration 2): added decreases clause for loop termination */
        decreases idx - i + 1
    {
        if a[idx] == x {
            k := idx;
        }
        idx := idx - 1;
    }
}